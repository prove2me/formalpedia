-- Prove2me | Theorems.Thm_SmallBiasPRF_lemma_31
-- name    : SmallBiasPRF.lemma_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:03.930198+00:00
-- url     : https://prove2.me/theorems/5489f4bf-4ba3-4ebf-88ce-cd046a956b3e
-- title:
--   Lemma 31 — the main expander lemma, $(99/100)^{|J|/2}$
-- statement:
--   Let $\Gamma$ be an undirected $d$-regular multigraph on $[m_1]$ with second largest singular value $\lambda\le1/192$, $A\subseteq\{0,1\}^n$ nonempty, $\{S_a\}_{a\in A}$ with $S_a\subseteq[m_2]$ and $|S_a|\ge4096(n+m_1)$, and $H$ a linear code of minimum relative distance at least $7/16$. Denote the overall active-coordinate set by $J=\{j\in[m_2]:A_j\neq\emptyset\}=\bigcup_{a\in A}S_a$. Then
--
--   $$\Big\|\mathop{\mathbb E}_{(x_1,\dots,x_{m_2})\sim\mu^{m_2}_\Gamma}\big[K_{A_1,x_1}\cdots K_{A_{m_2},x_{m_2}}\big]\Big\|_{op}\ \le\ \Big(\frac{99}{100}\Big)^{|J|/2}.$$
--
--   It is Theorem 32 with $\gamma=95/96$ (Lemma 16) and $\lambda_0=\lambda$, since $1-(191/192)^2/96<99/100$; with Lemma 13 for the walk law it gives Theorem 8.
--
--   **Formalization Note** $\mu^{m_2}_\Gamma$ is the stationary walk law; $J$ is written as $\{j:A_j\ne\emptyset\}$. $(99/100)^{|J|/2}$ is a real power.
--
--   Differences from the source:
--   - generalization: Γ a finite undirected d-regular multigraph on [m₁] with labelled incidences → NB : Fin m₁ → Fin d → Fin m₁ with symmetric incidence counts #{e : NB x e = y} = #{e : NB y e = x} (IsUndirected); reason: the proof uses only the symmetry and regularity of the adjacency matrix; every undirected d-regular multigraph satisfies the condition, which in addition admits an odd number of loop incidences at a vertex
--   - encoding: second largest singular value λ ≤ 1/192, defined as ‖E_Γ − U‖_op = λ on L²(Ω) with the uniform probability measure → ‖adjMatrix NB − avgMatrix‖ ≤ 1/192 in the Euclidean operator norm of real matrices (IsSpectralExpander); reason: the paper's own definition; rescaling the inner product does not change operator norms
--   - encoding: H a linear code of minimum relative distance at least 7/16 → H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2) with (7/16)·m₁ ≤ wt(H v) for all v ≠ 0 (HasMinRelDist); reason: for a linear code the minimum distance is the minimum weight of a nonzero codeword; same instances
--   - encoding: operators on functions W → ℝ with the normalized inner product E_{S∈W}[f g]; operator norm ‖·‖_op → real matrices indexed by W, composition = matrix product, Euclidean L² operator norm (Matrix.Norms.L2Operator); reason: the normalized and Euclidean inner products differ by the constant |W|, so adjoints and operator norms coincide
--   - encoding: the stationary walk distribution μ^m (uniform initial vertex, each step one transition of E_Γ) and the expectation of f₁(y₁)⋯f_m(y_m) under it → walkLaw NB m y = |Ω|⁻¹ ∏_{i+1<m} E_Γ[y_i, y_{i+1}] and Σ_y walkLaw(y) · (List.ofFn …).prod, leftmost factor = coordinate 1; reason: the law of the stationary chain with transition matrix E_Γ, products in chronological order; same distribution and same operator
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 31, p.37 (PDF 40)

import Mathlib
import Definitions.Def_SmallBiasPRF_HasMinRelDist
import Definitions.Def_SmallBiasPRF_IsSpectralExpander
import Definitions.Def_SmallBiasPRF_KB

open scoped Matrix.Norms.L2Operator

namespace SmallBiasPRF

/-- **Lemma 31** (main expander lemma), p.37 (PDF p.40).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 31, p.37 (PDF p.40).

In the setting of Theorem 8 (`Γ` an undirected `d`-regular multigraph on `[m₁]` with
`λ ≤ 1/192`, `A ⊆ {0,1}ⁿ` nonempty, `|S_a| ≥ 4096(n + m₁)` for `a ∈ A`, and `H` a linear code of
minimum relative distance at least `7/16`), denote the overall active-coordinate set by
`J = {j ∈ [m₂] : A_j ≠ ∅} = ⋃_{a∈A} S_a`. Then
`‖E_{(x₁,…,x_{m₂})∼μ^{m₂}_Γ}[K_{A₁,x₁} ⋯ K_{A_{m₂},x_{m₂}}]‖_op ≤ (99/100)^{|J|/2}`.

**Formalization Note.** `μ^{m₂}_Γ` is the stationary walk law `walkLaw NB m₂`; the expectation is
the weighted sum of matrix products in chronological order (`List.ofFn`). `J` is written with its
first definition, `{j : A_j ≠ ∅}`. Operators are matrices indexed by `W` with the Euclidean
operator norm; `(99/100)^{|J|/2}` is a real power. -/
theorem lemma_31 (n m₁ m₂ d : ℕ) [NeZero n] [NeZero m₁] [NeZero d]
    (NB : Fin m₁ → Fin d → Fin m₁) (hund : IsUndirected NB)
    (hspec : IsSpectralExpander NB (1 / 192))
    (A : Finset (Fin n → ZMod 2)) (hA : A.Nonempty) (Sfam : (Fin n → ZMod 2) → Finset (Fin m₂))
    (hS : ∀ a ∈ A, 4096 * (n + m₁) ≤ (Sfam a).card)
    (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2)) (hH : HasMinRelDist H (7 / 16)) :
    ‖∑ x : Fin m₂ → Fin m₁,
        walkLaw NB m₂ x • (List.ofFn fun j => KBx H A (activeSet A Sfam j) (x j)).prod‖ ≤
      (99 / 100 : ℝ) ^
        (((Finset.univ.filter fun j : Fin m₂ => (activeSet A Sfam j).Nonempty).card : ℝ) / 2) := by sorry

end SmallBiasPRF

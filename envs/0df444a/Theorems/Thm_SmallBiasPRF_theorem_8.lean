-- Prove2me | Theorems.Thm_SmallBiasPRF_theorem_8
-- name    : SmallBiasPRF.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:17.370919+00:00
-- url     : https://prove2.me/theorems/ddb270b6-9991-477a-be78-95f3da767209
-- title:
--   Theorem 8 — single-bit bias of the short-key construction
-- statement:
--   Let $\Gamma$ be an undirected $d$-regular multigraph on $[m_1]$ whose second largest singular value is $\lambda\le1/192$. Fix a nonempty $A\subseteq\{0,1\}^n$ and subsets $\{S_a\}_{a\in A}$ of $[m_2]$ with $|S_a|\ge 4096(n+m_1)$ for every $a\in A$. Then for every linear code $H:\mathbb F_2^n\to\mathbb F_2^{m_1}$ of minimum relative distance at least $7/16$,
--
--   $$\Big|\mathop{\mathbb E}_{k_e,w,z}\Big[(-1)^{\sum_{a\in A}\tilde F^{S_a}_{k_e,w,z}(a)}\Big]\Big|\ \le\ \mathop{\mathbb E}_{k_e,w}\Big[\Big|\mathop{\mathbb E}_{z}\Big[(-1)^{\sum_{a\in A}\tilde F^{S_a}_{k_e,w,z}(a)}\Big]\Big|\Big]\ \le\ 2^{-2n}.\tag{4}$$
--
--   With Lemma 10 this gives Theorem 7; no compression map $R$ is involved.
--
--   **Formalization Note** $k_e$, $w$, $z$ are independent and uniform; both inequalities are stated.
--
--   Differences from the source:
--   - generalization: Γ a finite undirected d-regular multigraph on [m₁] with labelled incidences → NB : Fin m₁ → Fin d → Fin m₁ with symmetric incidence counts #{e : NB x e = y} = #{e : NB y e = x} (IsUndirected); reason: the proof uses only the symmetry and regularity of the adjacency matrix; every undirected d-regular multigraph satisfies the condition, which in addition admits an odd number of loop incidences at a vertex
--   - encoding: second largest singular value λ ≤ 1/192, defined as ‖E_Γ − U‖_op = λ on L²(Ω) with the uniform probability measure → ‖adjMatrix NB − avgMatrix‖ ≤ 1/192 in the Euclidean operator norm of real matrices (IsSpectralExpander); reason: the paper's own definition; rescaling the inner product does not change operator norms
--   - encoding: H a linear code of minimum relative distance at least 7/16 → H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2) with (7/16)·m₁ ≤ wt(H v) for all v ≠ 0 (HasMinRelDist); reason: for a linear code the minimum distance is the minimum weight of a nonzero codeword; same instances
--   - encoding: 1-based indices; s_j defined recursively mod 3; t_j = ((s_j + z_j) mod 3) mod 2; keys in {0,1,2}^{m₂} → 0-based Fin indices; s_j = Σ_{i≤j} b_i w_i in ZMod 3 with bits lifted by value; t_j from the representative (s_j + z_j).val; keys Fin m₂ → ZMod 3; reason: Lean convention; the prefix sum is the unrolled recursion, and .val is the canonical representative in {0,1,2}; same function
--   - encoding: k_e = (x₁, e₁, …, e_{m₂−1}) ∈ Ω × [d]^{m₂−1}, x_{j+1} = NB(x_j, e_j), key uniform → KeyExp = Fin m₁ × (Fin (m₂ − 1) → Fin d), walk 0 = x₁, walk (j+1) = NB (walk j) (e j); uniform key = PMF.uniformOfFintype / uavg over the finite key type; reason: 0-based indexing; m₂ ≥ 1 under the hypotheses, so the same walk and the same uniform law
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Theorem 8, display (4), p.16 (PDF 19)

import Mathlib
import Definitions.Def_SmallBiasPRF_GeneratesBiasedSpace
import Definitions.Def_SmallBiasPRF_HasMinRelDist
import Definitions.Def_SmallBiasPRF_Ftilde

namespace SmallBiasPRF

/-- **Theorem 8** (single-bit short-key bias), display (4), p.16 (PDF p.19).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Theorem 8, p.16 (PDF p.19).

Let `Γ` be an undirected `d`-regular multigraph on `[m₁]` whose second largest singular value is
`λ ≤ 1/192`. Fix a nonempty `A ⊆ {0,1}ⁿ` and subsets `{S_a}_{a∈A}`, `S_a ⊆ [m₂]`, with
`|S_a| ≥ 4096(n + m₁)` for every `a ∈ A`. Then, for every linear code `H : 𝔽₂ⁿ → 𝔽₂^{m₁}` of
minimum relative distance at least `7/16`,
`|E_{k_e,w,z}[(−1)^{∑_{a∈A} F̃^{S_a}_{k_e,w,z}(a)}]| ≤ E_{k_e,w}[|E_z[(−1)^{∑_{a∈A} F̃^{S_a}_{k_e,w,z}(a)}]|] ≤ 2^{−2n}`.

**Formalization Note.** `k_e`, `w`, `z` are independent and uniform on `KeyExp m₁ m₂ d`,
`Fin m₂ → ZMod 3`, `Fin m₂ → ZMod 3`; expectations are uniform averages (`uavg`). `Γ` is encoded as
in Theorem 7. No `R` occurs. Both inequalities of (4) are stated. -/
theorem theorem_8 (n m₁ m₂ d : ℕ) [NeZero n] [NeZero m₁] [NeZero d]
    (NB : Fin m₁ → Fin d → Fin m₁) (hund : IsUndirected NB)
    (hspec : IsSpectralExpander NB (1 / 192))
    (A : Finset (Fin n → ZMod 2)) (hA : A.Nonempty) (Sfam : (Fin n → ZMod 2) → Finset (Fin m₂))
    (hS : ∀ a ∈ A, 4096 * (n + m₁) ≤ (Sfam a).card)
    (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2)) (hH : HasMinRelDist H (7 / 16)) :
    |uavg fun κ : FullKey m₁ m₂ d =>
        paritySign (∑ a ∈ A, FtildeS H NB (Sfam a) κ.1 κ.2.1 κ.2.2 a)| ≤
        uavg (fun kw : KeyExp m₁ m₂ d × (Fin m₂ → ZMod 3) =>
          |uavg fun z : Fin m₂ → ZMod 3 => paritySign (∑ a ∈ A, FtildeS H NB (Sfam a) kw.1 kw.2 z a)|) ∧
      uavg (fun kw : KeyExp m₁ m₂ d × (Fin m₂ → ZMod 3) =>
          |uavg fun z : Fin m₂ → ZMod 3 => paritySign (∑ a ∈ A, FtildeS H NB (Sfam a) kw.1 kw.2 z a)|) ≤
        (2 : ℝ) ^ (-(2 * (n : ℤ))) := by sorry

end SmallBiasPRF

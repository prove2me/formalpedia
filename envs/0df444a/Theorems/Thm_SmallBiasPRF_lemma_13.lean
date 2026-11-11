-- Prove2me | Theorems.Thm_SmallBiasPRF_lemma_13
-- name    : SmallBiasPRF.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:48.131429+00:00
-- url     : https://prove2.me/theorems/e5d00edc-95d3-4897-907e-7b6a29307a12
-- title:
--   Lemma 13 — the bias is bounded by an operator norm
-- statement:
--   In the generalized construction with selector law $\nu$, with $A$, $\{S_a\}$, $A_j$ and $K_{B,x}$ as in §5.1–5.3,
--
--   $$\mathop{\mathbb E}_{\pi\sim\nu,w}\Big[\Big|\mathop{\mathbb E}_{z}\Big[(-1)^{\sum_{a\in A}F^{S_a}_{\pi,w,z}(a)}\Big]\Big|\Big]\ \le\ 3^{m_1/4}\,\Big\|\mathop{\mathbb E}_{\pi\sim\nu}\big[K_{A_1,\pi(1)}\cdots K_{A_{m_2},\pi(m_2)}\big]\Big\|_{op}^{1/2},$$
--
--   where the operators are composed in chronological order, left to right. The factor $3^{m_1/4}$ comes from $|W|\le 3^{m_1}$. For the walk law this is Lemma 30, which feeds the expander lemma (Lemma 31).
--
--   **Formalization Note** The expectation of operators is the $\nu$-weighted sum of matrix products; $3^{m_1/4}$ and the square root are real powers.
--
--   Differences from the source:
--   - generalization: A and {S_a}_{a∈A} as in Theorem 6 (A nonempty, |S_a| ≥ 4096(n + m₁)) and H of minimum relative distance at least 7/16 (standing in §5) → A any finite set of inputs, {S_a} any family of subsets of [m₂], H any linear map; reason: the statement and its proof use none of these properties; the paper's setting is a special case
--   - encoding: operators on functions W → ℝ with the normalized inner product E_{S∈W}[f g]; operator norm ‖·‖_op → real matrices indexed by W, composition = matrix product, Euclidean L² operator norm (Matrix.Norms.L2Operator); reason: the normalized and Euclidean inner products differ by the constant |W|, so adjoints and operator norms coincide
--   - encoding: 1-based indices; s_j defined recursively mod 3; t_j = ((s_j + z_j) mod 3) mod 2; keys in {0,1,2}^{m₂} → 0-based Fin indices; s_j = Σ_{i≤j} b_i w_i in ZMod 3 with bits lifted by value; t_j from the representative (s_j + z_j).val; keys Fin m₂ → ZMod 3; reason: Lean convention; the prefix sum is the unrolled recursion, and .val is the canonical representative in {0,1,2}; same function
--   - encoding: π ∈ [m₁]^{m₂} sampled from an arbitrary distribution ν independently of the uniform (w, z) → ν : PMF (Fin m₂ → Fin m₁); the joint law is ν bound with the uniform law on (w, z) (selKeyLaw ν), or pmfExp ν of uniform averages over w and z; reason: this is the product law the page describes; same distribution
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 13, p.21 (PDF 24)

import Mathlib
import Definitions.Def_SmallBiasPRF_GeneratesBiasedSpace
import Definitions.Def_SmallBiasPRF_basicF
import Definitions.Def_SmallBiasPRF_KB

open scoped Matrix.Norms.L2Operator

namespace SmallBiasPRF

/-- **Lemma 13** (operator reduction), p.21 (PDF p.24).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 13, p.21 (PDF p.24).

In the generalized construction in which `π ∈ [m₁]^{m₂}` is sampled from an arbitrary distribution
`ν` independently of the other variables,
`E_{π∼ν,w}[|E_z[(−1)^{∑_{a∈A} F^{S_a}_{π,w,z}(a)}]|] ≤ 3^{m₁/4} ‖E_{π∼ν}[K_{A₁,π(1)} ⋯ K_{A_{m₂},π(m₂)}]‖_op^{1/2}`.

**Formalization Note.** Operators on `L²(W)` are real matrices indexed by `W` (`KBx`); the
product is in chronological order, left to right (`List.ofFn`, index `0` = the paper's
coordinate `1`), and `E_{π∼ν}` is the `ν`-weighted sum of matrices. `‖·‖` is the Euclidean
operator norm (equal to the norm for the paper's normalized inner product). `3^{m₁/4}` and the
square root are real powers. `A`, `{S_a}` and `H` are arbitrary (the paper fixes them "as in
Theorem 6", which the proof does not use). -/
theorem lemma_13 (n m₁ m₂ : ℕ) [NeZero n] [NeZero m₁] [NeZero m₂]
    (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2)) (A : Finset (Fin n → ZMod 2))
    (Sfam : (Fin n → ZMod 2) → Finset (Fin m₂)) (ν : PMF (Fin m₂ → Fin m₁)) :
    pmfExp ν (fun π => uavg fun w : Fin m₂ → ZMod 3 =>
        |uavg fun z : Fin m₂ → ZMod 3 => paritySign (∑ a ∈ A, basicFS H (Sfam a) π w z a)|) ≤
      (3 : ℝ) ^ ((m₁ : ℝ) / 4) *
        ‖∑ π : Fin m₂ → Fin m₁,
            (ν π).toReal • (List.ofFn fun j => KBx H A (activeSet A Sfam j) (π j)).prod‖ ^
          (1 / 2 : ℝ) := by sorry

end SmallBiasPRF

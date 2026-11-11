-- Prove2me | Theorems.Thm_SmallBiasPRF_lemma_11
-- name    : SmallBiasPRF.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:29.984133+00:00
-- url     : https://prove2.me/theorems/2ab26692-c379-404d-aed6-d3ffdaa726f5
-- title:
--   Lemma 11 — expansion of the single-bit bias by coordinates
-- statement:
--   In the generalized construction with selector law $\nu$, let $A\subseteq\{0,1\}^n$, $\{S_a\}_{a\in A}$ with $S_a\subseteq[m_2]$, let $\tilde S_j$ be the vectorized states and $A_j=\{a\in A:j\in S_a\}$ the active sets. Then
--
--   $$\mathop{\mathbb E}_{\pi\sim\nu,w}\Big[\Big|\mathop{\mathbb E}_{z}\Big[(-1)^{\sum_{a\in A}F^{S_a}_{\pi,w,z}(a)}\Big]\Big|\Big]=\mathop{\mathbb E}_{\pi\sim\nu,w}\Big[\prod_{j\in[m_2]}\big|\Lambda_{A_j}(\tilde S_j|_{A_j})\big|\Big].\tag{8}$$
--
--   The identity isolates the randomness of $z$ coordinate by coordinate and is the starting point of the operator analysis.
--
--   **Formalization Note** $w$ and $z$ are uniform on $\{0,1,2\}^{m_2}$; $\mathbb E_{\pi\sim\nu}$ is the expectation under the probability mass function $\nu$.
--
--   Differences from the source:
--   - generalization: A and {S_a}_{a∈A} as in Theorem 6 (A nonempty, |S_a| ≥ 4096(n + m₁)) and H of minimum relative distance at least 7/16 (standing in §5) → A any finite set of inputs, {S_a} any family of subsets of [m₂], H any linear map; reason: the statement and its proof use none of these properties; the paper's setting is a special case
--   - encoding: 1-based indices; s_j defined recursively mod 3; t_j = ((s_j + z_j) mod 3) mod 2; keys in {0,1,2}^{m₂} → 0-based Fin indices; s_j = Σ_{i≤j} b_i w_i in ZMod 3 with bits lifted by value; t_j from the representative (s_j + z_j).val; keys Fin m₂ → ZMod 3; reason: Lean convention; the prefix sum is the unrolled recursion, and .val is the canonical representative in {0,1,2}; same function
--   - encoding: π ∈ [m₁]^{m₂} sampled from an arbitrary distribution ν independently of the uniform (w, z) → ν : PMF (Fin m₂ → Fin m₁); the joint law is ν bound with the uniform law on (w, z) (selKeyLaw ν), or pmfExp ν of uniform averages over w and z; reason: this is the product law the page describes; same distribution
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 11, display (8), p.19 (PDF 22)

import Mathlib
import Definitions.Def_SmallBiasPRF_GeneratesBiasedSpace
import Definitions.Def_SmallBiasPRF_basicF
import Definitions.Def_SmallBiasPRF_KB

namespace SmallBiasPRF

/-- **Lemma 11** (expansion by coordinates), display (8), p.19 (PDF p.22).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 11, p.19 (PDF p.22).

In the generalized construction in which `π ∈ [m₁]^{m₂}` is sampled from an arbitrary distribution
`ν` independently of the other variables,
`E_{π∼ν,w}[|E_z[(−1)^{∑_{a∈A} F^{S_a}_{π,w,z}(a)}]|] = E_{π∼ν,w}[∏_{j∈[m₂]} |Λ_{A_j}(S̃_j|_{A_j})|]`,
where `S̃_j` are the vectorized states (5) and `A_j = {a ∈ A : j ∈ S_a}` the active sets.

**Formalization Note.** `w, z` are uniform on `Fin m₂ → ZMod 3` (`uavg`); `E_{π∼ν}` is
`pmfExp ν`. `A` is any finite set of inputs, `{S_a}` any family of subsets of `[m₂]` and `H` any
linear map: the paper fixes them "as in Theorem 6" (A nonempty, `|S_a| ≥ 4096(n + m₁)`, `H` of
relative distance `≥ 7/16`) but the identity uses none of these. -/
theorem lemma_11 (n m₁ m₂ : ℕ) [NeZero n] [NeZero m₁] [NeZero m₂]
    (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2)) (A : Finset (Fin n → ZMod 2))
    (Sfam : (Fin n → ZMod 2) → Finset (Fin m₂)) (ν : PMF (Fin m₂ → Fin m₁)) :
    pmfExp ν (fun π => uavg fun w : Fin m₂ → ZMod 3 =>
        |uavg fun z : Fin m₂ → ZMod 3 => paritySign (∑ a ∈ A, basicFS H (Sfam a) π w z a)|) =
      pmfExp ν (fun π => uavg fun w : Fin m₂ → ZMod 3 =>
        ∏ j : Fin m₂, |Lambda (activeSet A Sfam j) (stateVec H A π w j)|) := by sorry

end SmallBiasPRF

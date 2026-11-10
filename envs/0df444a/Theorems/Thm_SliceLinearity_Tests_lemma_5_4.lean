-- Prove2me | Theorems.Thm_SliceLinearity_Tests_lemma_5_4
-- name    : SliceLinearity.Tests.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:39:23.197016+00:00
-- url     : https://prove2.me/theorems/15c57d87-dbc4-40b3-b115-2cb65ffe6d09
-- title:
--   Lemma 5.4 — Hölder for random active sets (sizes two, three and four)
-- statement:
--   Let $A_1,\dots,A_n\subseteq[m]$ be the active sets of the test: independent across coordinates, each of size $a\in\{2,3,4\}$ with probability $\pi_a$ and uniform given its size. Let $I_j=\{i:j\in A_i\}$. For nonnegative functions $b_j$ on subsets of $[n]$,
--   $$\mathbb E\Big[\prod_{j=1}^m b_j(I_j)\Big]\le\prod_{j=1}^m\mathbb E\big[b_j(I_j)^2\big]^{1/2}.$$
--   The proof states the inequality with active sets of size four allowed, as Lemma 6.13 needs ("We also prove the inequality when active sets of size four are allowed").
--
--   Differences from the source:
--   - generalization: the active sets of the active-set test (pairs with probability 1 − θ, triples with probability θ, m = ⌈1/p*⌉) → any m ≥ 2 and any size probabilities π₂, π₃, π₄ ≥ 0 summing to 1 with π_a = 0 for a > m; reason: the proof proves this form (sizes up to four, used by Lemma 6.13); the test is π₂ = 1 − θ, π₃ = θ, π₄ = 0, and θ > 0 forces m ≥ 3
--   - encoding: expectations over the active sets → finite sums over A : Fin n → Finset (Fin m) weighted by activeSetsJoint; reason: the active sets are independent across coordinates; same law
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §5.1, p. 31 (PDF 33), Lemma 5.4 (and its proof, pp. 31–32, PDF 33–34)

import Mathlib
import Definitions.Def_SliceLinearity_Tests_ActiveSet

set_option autoImplicit false

namespace SliceLinearity.Tests

/-- **Lemma 5.4** (Hölder for random active sets), p. 31 (PDF 33), in the form its proof establishes
(active sets of size two, three or four, as needed in Lemma 6.13). The active sets `A₁, …, A_n ⊆ [m]`
are independent, each of size `a ∈ {2, 3, 4}` with probability `π a` and uniform given its size; let
`I_j = {i : j ∈ Aᵢ}`. For nonnegative functions `b_j` on subsets of `[n]`,
`E[∏_j b_j(I_j)] ≤ ∏_j E[b_j(I_j)²]^{1/2}`. -/
theorem lemma_5_4 {m n : ℕ} (hm : 2 ≤ m) (π : ℕ → ℝ) (hπ2 : 0 ≤ π 2) (hπ3 : 0 ≤ π 3)
    (hπ4 : 0 ≤ π 4) (hπsum : π 2 + π 3 + π 4 = 1) (hπm : ∀ a, m < a → π a = 0)
    (b : Fin m → Finset (Fin n) → ℝ) (hb : ∀ j I, 0 ≤ b j I) :
    ∑ A : Fin n → Finset (Fin m), activeSetsJoint m π A * ∏ j, b j (coordSet A j) ≤
      ∏ j, Real.sqrt (∑ A : Fin n → Finset (Fin m), activeSetsJoint m π A * b j (coordSet A j) ^ 2) := by sorry

end SliceLinearity.Tests

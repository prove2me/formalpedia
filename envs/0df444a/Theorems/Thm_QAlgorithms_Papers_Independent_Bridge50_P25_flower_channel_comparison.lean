-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_flower_channel_comparison
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.flower_channel_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:12:07.905967+00:00
-- url     : https://prove2.me/theorems/1fab932d-c4fb-4003-b445-19b2f1a1463d
-- title:
--   Unnumbered VI A: flower-channel capacity-bound separation
-- statement:
--   For each positive integer $d$, let $T_f^{(d)}:M_{2d}\to M_{2d}$ be the unital channel whose normalized Choi state is the DFT flower state of (24), on the cut $AA':BB'$ with dimensions $d,2,d,2$. Let $\widetilde T_f^{(d)}=\operatorname{Tr}_{B'}\circ T_f^{(d)}$. It is entanglement breaking, and $E_{\max}(\widetilde T_f^{(d)})=0$. With $Q_{\leftrightarrow}$ the operational two-way quantum capacity, $E_{\rm sq}$ the channel squashed entanglement, $E_C$ the channel formation regularization, and $\vartheta$ output transposition, one has
--
--   $$Q_{\leftrightarrow}(T_f^{(d)})\le E_{\max}(T_f^{(d)})\le2,$$
--   $$\log_2\|\vartheta\circ T_f^{(d)}\|_\diamond\ge\log_2(\sqrt d+1),\qquad E_C(T_f^{(d)})\ge E_{\rm sq}(T_f^{(d)})\ge1+\tfrac12\log_2d.$$
--
--   The squashed-entanglement and cost bounds strictly exceed $2$ when $d>4$, and the transposition bound strictly exceeds $2$ when $d>9$. For every real $g>0$, all sufficiently large $d$ make all three bounds exceed $2+g$.
--
--   This is an unbounded improvement in upper bounds, without asserting divergence of capacity. The identities (25),(26) are cited background. The printed squashed/cost threshold $d>2$ is corrected to $d>4$.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 19, Unnumbered VI A

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Section VI.A, PDF pp.18--19, (27): all bounds concern the SAME computed
DFT flower channel. Printed: d>2 for the squashed/cost improvement. Changed:
d>4, since 1+(log2 d)/2>2 iff d>4. The transposition threshold d>9 is unchanged.
The improvements of bounds are unbounded, not the quantum capacity itself.
Background flower-state values (25),(26) are used, not claimed as new results.
Independent moderation of the threshold correction is required. -/
theorem flower_channel_comparison :
    (∀ n : ℕ,
      let T := flowerChannel (n + 1)
      IsChannel T ∧ T 1 = 1 ∧ normalizedChannelChoi T = flowerMatrix (n + 1) ∧
      BreaksEntanglementAllReferences (reducedChannel T) ∧ channelEMax (reducedChannel T) = 0 ∧
      twoWayGenerationCapacity T false ≤ channelEMax T ∧ channelEMax T ≤ 2 ∧
      Real.logb 2 (Real.sqrt ((n + 1 : ℕ) : ℝ) + 1) ≤ transpositionBound T ∧
      ((1 + Real.logb 2 ((n + 1 : ℕ) : ℝ) / 2 : ℝ) : EReal) ≤ channelSquashed T ∧
      channelSquashed T ≤ regularizedFormationCost T ∧
      (4 < n + 1 → (2 : EReal) < channelSquashed T ∧ (2 : EReal) < regularizedFormationCost T) ∧
      (9 < n + 1 → (2 : ℝ) < transpositionBound T)) ∧
    (∀ gap : ℝ, 0 < gap → ∃ threshold : ℕ, ∀ n ≥ threshold,
      let T := flowerChannel (n + 1)
      (2 + gap : ℝ) < transpositionBound T ∧
      ((2 + gap : ℝ) : EReal) < channelSquashed T ∧
      ((2 + gap : ℝ) : EReal) < regularizedFormationCost T) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_strict_channel_class_inclusions
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.strict_channel_class_inclusions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:25:14.19129+00:00
-- url     : https://prove2.me/theorems/57f651f0-6b81-4a51-8661-f51571f11c5b
-- title:
--   Two strict channel-class inclusions
-- statement:
--   Across all positive finite input and output matrix dimensions, let CQ denote classical-quantum channels and let essentially CQ denote measure-and-prepare channels with norm-one POVM effects. Then
--   $$\mathrm{CQ}\subsetneq\mathrm{essentially\ CQ}\subsetneq\{T:T\text{ is entanglement breaking and }\operatorname{Im}T\text{ is polytopic}\}.$$
--   The inclusions hold for every quantum channel in every such dimension. Each strictness assertion has its own finite-dimensional channel witness: one essentially CQ channel that is not CQ, and one entanglement-breaking channel with polytopic image that is not essentially CQ. Strictness is not asserted in each fixed dimension.
--
--   This records both separations stated in the abstract.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 1, Abstract and §7: strict inclusions among channel classes

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P01

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P01

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Information100.P07 (projection)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- Abstract, PDF p.1, Definition 2.1, PDF p.3, and §7, PDF pp.12–14: inclusions and
both strictness witnesses across positive finite dimensions, not at every fixed dimension. -/
theorem strict_channel_class_inclusions :
    (∀ d n : ℕ, 0 < d → 0 < n → ∀ T : Superop (Fin d) (Fin n), IsChannel T →
      (HasCQRepresentation T → IsEssentialCQ T) ∧
      (IsEssentialCQ T → IsEB T ∧ IsPolytopic (channelImage T))) ∧
    (∃ d n : ℕ, 0 < d ∧ 0 < n ∧ ∃ T : Superop (Fin d) (Fin n),
      IsChannel T ∧ IsEssentialCQ T ∧ ¬ HasCQRepresentation T) ∧
    (∃ d n : ℕ, 0 < d ∧ 0 < n ∧ ∃ T : Superop (Fin d) (Fin n),
      IsChannel T ∧ IsEB T ∧ IsPolytopic (channelImage T) ∧ ¬ IsEssentialCQ T) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end

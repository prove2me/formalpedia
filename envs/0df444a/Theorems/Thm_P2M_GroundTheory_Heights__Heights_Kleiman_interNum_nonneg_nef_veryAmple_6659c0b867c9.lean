-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_interNum_nonneg_nef_veryAmple_6659c0b867c9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_interNum_nonneg_nef_veryAmple_6659c0b867c9
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:01:18.066452+00:00
-- url     : https://prove2.me/theorems/bbd3b902-2d88-4be3-b8e1-1516e5b85059
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman inter Num nonneg nef very Ample 6659c0b867c9: P2 M Ground Theory Heights  Heights Kleiman inter Num nonneg nef very Ample 6659c0b867c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman inter Num nonneg nef very Ample 6659c0b867c9 construction uses the P2 M Ground Theory Heights  Heights Kleiman inter Num nonneg nef very Ample 6659c0b867c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LeadingCoeffPosCut.lean#L18-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LeadingCoeffPosCut.lean#L18-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLeadingCoeffPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (hR : GenericPointSectionInput.Statement.{u, w})
include hR

theorem P2M_GroundTheory_Heights__Heights_Kleiman_interNum_nonneg_nef_veryAmple_6659c0b867c9 : ∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin (n + 1) → LineBundle k x),
    IsSubvar x pp (n + 1) → Nef (L 0).toSubSystem → (∀ i, i ≠ 0 → IsVeryAmple (L i).toSubSystem) →
      0 ≤ interNum pp (fun i => (L i).toSubSystem) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«interNum_nonneg_nef_veryAmple» := P2M_GroundTheory_Heights__Heights_Kleiman_interNum_nonneg_nef_veryAmple_6659c0b867c9

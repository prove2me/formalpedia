-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_nef_of_isVeryAmple_718fb75e12f6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_nef_of_isVeryAmple_718fb75e12f6
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:26.174995+00:00
-- url     : https://prove2.me/theorems/e4d8104e-f2fe-4c4c-8f04-2f5e16f49c7b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman nef of is Very Ample 718fb75e12f6: P2 M Ground Theory Heights  Heights Kleiman nef of is Very Ample 718fb75e12f6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman nef of is Very Ample 718fb75e12f6 construction uses the P2 M Ground Theory Heights  Heights Kleiman nef of is Very Ample 718fb75e12f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLeadingCoeffPos.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLeadingCoeffPos.lean#L14-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleProductPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLeadingCoeffPos
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_nef_of_isVeryAmple_718fb75e12f6 (hR : GenericPointSectionInput.Statement.{u, w}) {k : Type u} [Field k] {Ω : Type w} [Field Ω]
    [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω} (L : LineBundle k x) (hL : IsVeryAmple L.toSubSystem) :
    Nef L.toSubSystem := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«nef_of_isVeryAmple» := P2M_GroundTheory_Heights__Heights_Kleiman_nef_of_isVeryAmple_718fb75e12f6

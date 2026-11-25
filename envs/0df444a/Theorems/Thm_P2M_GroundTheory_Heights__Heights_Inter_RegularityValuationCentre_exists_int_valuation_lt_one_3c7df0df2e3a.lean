-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_exists_int_valuation_lt_one_3c7df0df2e3a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_exists_int_valuation_lt_one_3c7df0df2e3a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:03.244976+00:00
-- url     : https://prove2.me/theorems/58186228-e3aa-5213-ba83-339554a8ca83
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre exists int valuation lt one 3c7df0df2e3a: P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre exists int valuati
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre exists int valuation lt one 3c7df0df2e3a construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre exists int valuation lt one 3c7df0df2e3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsIntValuationLtOne.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsIntValuationLtOne.lean#L19-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldLeLocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIntValuationLtOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_exists_int_valuation_lt_one_3c7df0df2e3a {F : Type*} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ∃ n : ℤ, n ≠ 0 ∧ v.valuation F (n : F) < 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityValuationCentre».«exists_int_valuation_lt_one» := P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_exists_int_valuation_lt_one_3c7df0df2e3a

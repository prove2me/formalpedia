-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityDenominator_isMultiHomog_C_6474a899c711
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityDenominator_isMultiHomog_C_6474a899c711
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:43.37242+00:00
-- url     : https://prove2.me/theorems/11778121-acd6-4c19-b465-88c0a1faf6be
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Denominator is Multi Homog C 6474a899c711: P2 M Ground Theory Heights  Heights Inter Regularity Denominator is Multi Homog C 6474a899c711
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Denominator is Multi Homog C 6474a899c711 construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Denominator is Multi Homog C 6474a899c711 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsBisAlt.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsBisAlt.lean#L16-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LogCardLocIdealUnitMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isMultiHomog_C_8aa21e557757

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

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityDenominator_isMultiHomog_C_6474a899c711 {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (n : ℤ) :
    IsMultiHomog (C n : MRing ι) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityDenominator».«isMultiHomog_C» := P2M_GroundTheory_Heights__Heights_Inter_RegularityDenominator_isMultiHomog_C_6474a899c711

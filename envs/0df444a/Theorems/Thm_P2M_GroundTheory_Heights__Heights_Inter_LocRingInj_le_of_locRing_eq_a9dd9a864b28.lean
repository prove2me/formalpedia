-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingInj_le_of_locRing_eq_a9dd9a864b28
-- name    : P2M_GroundTheory_Heights__Heights_Inter_LocRingInj_le_of_locRing_eq_a9dd9a864b28
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:44:10.176194+00:00
-- url     : https://prove2.me/theorems/95f48798-b47b-4974-853b-7eb7eff433a5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Loc Ring Inj le of loc Ring eq a9dd9a864b28: P2 M Ground Theory Heights  Heights Inter Loc Ring Inj le of loc Ring eq a9dd9a864b28
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Loc Ring Inj le of loc Ring eq a9dd9a864b28 construction uses the P2 M Ground Theory Heights  Heights Inter Loc Ring Inj le of loc Ring eq a9dd9a864b28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingInj.lean#L15-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingInj.lean#L15-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LogCardLocIdealUnitMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingInj
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

theorem P2M_GroundTheory_Heights__Heights_Inter_LocRingInj_le_of_locRing_eq_a9dd9a864b28 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P W W' : Ideal (MRing ι)} (hP : P.IsPrime) (hW : IsMultiProjPrime W) (hW' : IsMultiProjPrime W')
    (hPW : P ≤ W) (hPW' : P ≤ W') (heq : locRing P W = locRing P W') : W ≤ W' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«LocRingInj».«le_of_locRing_eq» := P2M_GroundTheory_Heights__Heights_Inter_LocRingInj_le_of_locRing_eq_a9dd9a864b28

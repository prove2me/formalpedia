-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_add_first_log_b381cb271c60
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_add_first_log_b381cb271c60
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:27:09.958847+00:00
-- url     : https://prove2.me/theorems/9b7bf713-702b-4386-8ece-ef77c7db14ef
-- title:
--   P2 M Ground Theory Heights  Heights Inter pts Integral add first log b381cb271c60: P2 M Ground Theory Heights  Heights Inter pts Integral add first log b381cb271c60
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pts Integral add first log b381cb271c60 construction uses the P2 M Ground Theory Heights  Heights Inter pts Integral add first log b381cb271c60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDeLeSemiPos.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDeLeSemiPos.lean#L58-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsRegLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsMonoSemiPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRegCurvBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDeLeSemiPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_add_first_log_b381cb271c60 (hAdd : PtsAddFirst.Statement) {Q : Ideal (MRing ι)} {e : ℕ}
    {L : Fin e → HermLine ι} {M N D : HermLine ι} (hQ : IsArithVar Q (e + 2))
    (hL : ∀ j, IsSmoothHerm (L j)) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N) (hD : IsSmoothHerm D)
    (hDa : D.a = 0) :
    ptsIntegral Q (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) (fun z => Real.log (D.h z)) =
      ptsIntegral Q (Fin.cons (fun z => Real.log (M.h z)) (pot L)) (fun z => Real.log (D.h z)) +
        ptsIntegral Q (Fin.cons (fun z => Real.log (N.h z)) (pot L)) (fun z => Real.log (D.h z)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ptsIntegral_add_first_log» := P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_add_first_log_b381cb271c60

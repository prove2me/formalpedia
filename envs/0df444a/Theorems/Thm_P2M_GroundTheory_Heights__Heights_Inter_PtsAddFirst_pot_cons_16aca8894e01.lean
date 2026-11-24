-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_pot_cons_16aca8894e01
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_pot_cons_16aca8894e01
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:13.868002+00:00
-- url     : https://prove2.me/theorems/5ef45330-02d2-4604-8f30-28e20b8238b6
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pts Add First pot cons 16aca8894e01: P2 M Ground Theory Heights  Heights Inter Pts Add First pot cons 16aca8894e01
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pts Add First pot cons 16aca8894e01 construction uses the P2 M Ground Theory Heights  Heights Inter Pts Add First pot cons 16aca8894e01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAddFirst.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAddFirst.lean#L54-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_pot_cons_16aca8894e01 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (M : HermLine ι) (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PtsAddFirst».«pot_cons» := P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_pot_cons_16aca8894e01

-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__a466d063bccb
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__a466d063bccb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:46.342922+00:00
-- url     : https://prove2.me/theorems/2b8d47de-f5b9-4285-a442-289da605ccfe
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry adens cont Diff At log  a466d063bccb: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry adens cont Diff At log  a466d063bccb
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry adens cont Diff At log  a466d063bccb construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry adens cont Diff At log  a466d063bccb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStA.lean#L255-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStA.lean#L255-L261

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
variable {J : Type} [Fintype J] {D : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__a466d063bccb {m : ConeMetric ℂ J} (hsm : IsSmoothMetric m) {γ' : (Fin D → ℂ) → J → ℂ}
    {v : Fin D → ℂ} (hγ' : AnalyticAt ℂ γ' v) (hne : γ' v ≠ 0) :
    ContDiffAt ℝ 2 (fun w => Real.log (m.ρ (γ' w))) v := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«adens_contDiffAt_logρ» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__a466d063bccb

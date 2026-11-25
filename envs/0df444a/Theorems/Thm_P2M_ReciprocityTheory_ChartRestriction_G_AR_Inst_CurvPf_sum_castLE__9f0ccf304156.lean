-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_sum_castLE__9f0ccf304156
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_sum_castLE__9f0ccf304156
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:27:36.150875+00:00
-- url     : https://prove2.me/theorems/dd89dd98-4a02-42b1-8dd9-65ec689bf865
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Inst Curv Pf sum cast LE  9f0ccf304156: P2 M Reciprocity Theory Chart Restriction G AR Inst Curv Pf sum cast LE  9f0ccf304156
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Inst Curv Pf sum cast LE  9f0ccf304156 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Inst Curv Pf sum cast LE  9f0ccf304156 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DiagonalCurvatureCoefficient.lean#L149-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DiagonalCurvatureCoefficient.lean#L149-L161

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_sum_castLE__9f0ccf304156 {M : Type} [AddCommMonoid M] (g : Fin r → M) :
    ∑ j : Fin m, g (Fin.castLE hm j) = ∑ k : Fin r, if (k : ℕ) < m then g k else 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Inst».«CurvPf».«sum_castLE'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_sum_castLE__9f0ccf304156

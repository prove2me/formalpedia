-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cd_lin
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cd_lin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:22.329867+00:00
-- url     : https://prove2.me/theorems/d33e347b-6c30-496b-b747-2291db202302
-- title:
--   Curv Pf: cd lin
-- statement:
--   The Curv Pf construction uses the cd lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DiagonalCurvatureCoefficient.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DiagonalCurvatureCoefficient.lean#L41-L45

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cd_lin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (a b : Fin n) :
    ContDiff ℝ 2 fun v : Fin 1 → ℂ => (1 + (c * v 0) • A) a b := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cd_conjT
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cd_conjT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:35.360625+00:00
-- url     : https://prove2.me/theorems/82dbf0ee-59b3-4047-9647-bc1b31e2ff8f
-- title:
--   Curv Pf: cd conj T
-- statement:
--   The Curv Pf construction uses the cd conj T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DiagonalCurvatureCoefficient.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DiagonalCurvatureCoefficient.lean#L22-L25

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cd_conjT {n : ℕ} (F : E → Matrix (Fin n) (Fin n) ℂ) (hF : ∀ a b, ContDiff ℝ k fun v => F v a b)
    (a b : Fin n) : ContDiff ℝ k fun v => (F v)ᴴ a b := by sorry

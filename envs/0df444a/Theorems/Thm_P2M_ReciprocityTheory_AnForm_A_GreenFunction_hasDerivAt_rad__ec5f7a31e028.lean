-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_rad__ec5f7a31e028
-- name    : P2M_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_rad__ec5f7a31e028
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:12.690183+00:00
-- url     : https://prove2.me/theorems/d52d354f-126a-5523-acdd-c2345e8c8152
-- title:
--   P2 M Reciprocity Theory An Form A Green Function has Deriv At rad  ec5f7a31e028: P2 M Reciprocity Theory An Form A Green Function has Deriv At rad  ec5f7a31e028
-- statement:
--   The P2 M Reciprocity Theory An Form A Green Function has Deriv At rad  ec5f7a31e028 construction uses the P2 M Reciprocity Theory An Form A Green Function has Deriv At rad  ec5f7a31e028 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L74-L80

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace intervalIntegral
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.GreenFunction
noncomputable section
variable {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ)
include hu

theorem P2M_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_rad__ec5f7a31e028 (e : ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => fderiv ℝ u (a + r • e) e)
      (fderiv ℝ (fderiv ℝ u) (a + r • e) e e) r := by sorry

alias «ReciprocityTheory».«AnForm».«A».«GreenFunction».«hasDerivAt_rad'» := P2M_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_rad__ec5f7a31e028

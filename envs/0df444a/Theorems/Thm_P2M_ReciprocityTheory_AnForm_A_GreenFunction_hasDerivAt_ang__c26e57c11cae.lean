-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_ang__c26e57c11cae
-- name    : P2M_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_ang__c26e57c11cae
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:39.471993+00:00
-- url     : https://prove2.me/theorems/3c304fa3-a3d9-4c68-9a0e-026e9d5e6182
-- title:
--   P2 M Reciprocity Theory An Form A Green Function has Deriv At ang  c26e57c11cae: P2 M Reciprocity Theory An Form A Green Function has Deriv At ang  c26e57c11cae
-- statement:
--   The P2 M Reciprocity Theory An Form A Green Function has Deriv At ang  c26e57c11cae construction uses the P2 M Reciprocity Theory An Form A Green Function has Deriv At ang  c26e57c11cae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L89-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L89-L101

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

theorem P2M_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_ang__c26e57c11cae (r θ : ℝ) :
    HasDerivAt (fun θ : ℝ => fderiv ℝ u (a + r • ee θ) (r • (Complex.I * ee θ)))
      (fderiv ℝ (fderiv ℝ u) (a + r • ee θ) (r • (Complex.I * ee θ)) (r • (Complex.I * ee θ))
        - r * fderiv ℝ u (a + r • ee θ) (ee θ)) θ := by sorry

alias «ReciprocityTheory».«AnForm».«A».«GreenFunction».«hasDerivAt_ang'» := P2M_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_ang__c26e57c11cae

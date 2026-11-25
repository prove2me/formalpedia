-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_gReg
-- name    : ReciprocityTheory.AnForm.A.hessC_gReg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:06:06.194977+00:00
-- url     : https://prove2.me/theorems/28ba7a6f-156a-42ab-be07-fee0faf2e77c
-- title:
--   A: hess C g Reg
-- statement:
--   The A construction uses the hess C g Reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L66-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L66-L97

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.AnForm.A.hessC_gReg {n : ℕ} {ε : ℝ} (hε : 0 < ε) (i : Fin (n + 1)) (z : Fin (n + 1) → ℂ) :
    hessC (fun y : Fin (n + 1) → ℂ => gReg ε (y i)) z =
      ((cReg ε (z i) : ℝ) : ℂ) • Matrix.single i i 1 := by sorry

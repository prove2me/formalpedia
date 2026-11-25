-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_cons_gReg
-- name    : ReciprocityTheory.AnForm.A.maDens_cons_gReg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:20:03.215299+00:00
-- url     : https://prove2.me/theorems/85ac78e5-4607-4ce0-ba03-8ceb2e8727e4
-- title:
--   A: ma Dens cons g Reg
-- statement:
--   The A construction uses the ma Dens cons g Reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L241-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L241-L250

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
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.A.maDens_cons_gReg {ε : ℝ} (hε : 0 < ε) (i : Fin (n + 1))
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) :
    maDens (Fin.cons (fun y => gReg ε (y i)) φ) z =
      kDens n * cReg ε (z i) * (1 / ((n : ℝ) + 1)) * minorDens i φ z := by sorry

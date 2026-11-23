-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_cons_continuous
-- name    : ReciprocityTheory.AnForm.A.maDens_cons_continuous
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:16.644867+00:00
-- url     : https://prove2.me/theorems/85337f95-3e65-40c8-9fdd-f7f0f8812cb1
-- title:
--   A: ma Dens cons continuous
-- statement:
--   The A construction uses the ma Dens cons continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L293-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L293-L306

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

theorem ReciprocityTheory.AnForm.A.maDens_cons_continuous {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    {f : (Fin (n + 1) → ℂ) → ℝ} (hf : ContDiff ℝ 3 f) (hfU : tsupport f ⊆ U)
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hφ : ∀ k, ContDiffOn ℝ ∞ (φ k) U) :
    Continuous (maDens (Fin.cons f φ)) := by sorry

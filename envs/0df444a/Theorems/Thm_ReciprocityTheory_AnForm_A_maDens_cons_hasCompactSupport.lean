-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_cons_hasCompactSupport
-- name    : ReciprocityTheory.AnForm.A.maDens_cons_hasCompactSupport
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:16.77774+00:00
-- url     : https://prove2.me/theorems/928c7fb9-880a-4c9a-bfb5-d68b14a2ab6f
-- title:
--   A: ma Dens cons has Compact Support
-- statement:
--   The A construction uses the ma Dens cons has Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L308-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L308-L310

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

theorem ReciprocityTheory.AnForm.A.maDens_cons_hasCompactSupport {f : (Fin (n + 1) → ℂ) → ℝ} (hf : HasCompactSupport f)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) : HasCompactSupport (maDens (Fin.cons f φ)) := by sorry

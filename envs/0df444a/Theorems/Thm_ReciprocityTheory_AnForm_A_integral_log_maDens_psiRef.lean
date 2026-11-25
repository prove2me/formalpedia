-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_integral_log_maDens_psiRef
-- name    : ReciprocityTheory.AnForm.A.integral_log_maDens_psiRef
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:06:50.622138+00:00
-- url     : https://prove2.me/theorems/7fd65172-d935-4729-913b-c1e422e6761a
-- title:
--   A: integral log ma Dens psi Ref
-- statement:
--   The A construction uses the integral log ma Dens psi Ref property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L130-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L130-L149

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt
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

theorem ReciprocityTheory.AnForm.A.integral_log_maDens_psiRef (i : Fin (n + 1)) {h : (Fin (n + 1) → ℂ) → ℝ}
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) :
    ∫ z, Real.log ‖z i‖ * maDens (Fin.cons h (psiRef n)) z =
      kDens n * ((Real.pi / 2) * (1 / ((n : ℝ) + 1)) * ∫ w, h (Fin.insertNth i 0 w)) := by sorry

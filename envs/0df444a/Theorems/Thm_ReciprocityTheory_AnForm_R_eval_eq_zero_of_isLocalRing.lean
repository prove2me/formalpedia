-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_eval_eq_zero_of_isLocalRing
-- name    : ReciprocityTheory.AnForm.R.eval_eq_zero_of_isLocalRing
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:14.17924+00:00
-- url     : https://prove2.me/theorems/e945ff79-fcd1-4028-bfa2-240f36701069
-- title:
--   R: eval eq zero of is Local Ring
-- statement:
--   The R construction uses the eval eq zero of is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChartA.lean#L56-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChartA.lean#L56-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.R.eval_eq_zero_of_isLocalRing (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    [IsLocalRing (locRing K p)] : ∀ k ∈ K, eval p k = 0 := by sorry

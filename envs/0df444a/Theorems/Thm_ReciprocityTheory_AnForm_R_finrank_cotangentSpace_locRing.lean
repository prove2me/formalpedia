-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_finrank_cotangentSpace_locRing
-- name    : ReciprocityTheory.AnForm.R.finrank_cotangentSpace_locRing
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:22.978779+00:00
-- url     : https://prove2.me/theorems/f25ec18c-7495-5783-9fd5-5b13c564bdb8
-- title:
--   R: finrank cotangent Space loc Ring
-- statement:
--   The R construction uses the finrank cotangent Space loc Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChart.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChart.lean#L47-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
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

theorem ReciprocityTheory.AnForm.R.finrank_cotangentSpace_locRing (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    [IsLocalRing (locRing K p)] :
    Module.finrank (IsLocalRing.ResidueField (locRing K p)) (IsLocalRing.CotangentSpace (locRing K p))
      + Module.finrank ℂ (jacSpan K p) = n := by sorry

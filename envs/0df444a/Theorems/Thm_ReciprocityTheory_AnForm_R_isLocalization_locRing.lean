-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isLocalization_locRing
-- name    : ReciprocityTheory.AnForm.R.isLocalization_locRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:58.230809+00:00
-- url     : https://prove2.me/theorems/5823384b-67d6-47ca-947c-8408ff62349c
-- title:
--   R: is Localization loc Ring
-- statement:
--   The R construction uses the is Localization loc Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocA.lean#L28-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocA.lean#L28-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
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

theorem ReciprocityTheory.AnForm.R.isLocalization_locRing {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (hK : K ≤ ptIdeal p) :
    letI := ptQ_isPrime hK; IsLocalization.AtPrime (locRing K p) (ptQ K p) := by sorry

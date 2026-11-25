-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_algebraMap_quot_mk
-- name    : ReciprocityTheory.AnForm.R.algebraMap_quot_mk
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:25.065121+00:00
-- url     : https://prove2.me/theorems/29b98e1e-3114-4538-8100-a7a66cad0fb9
-- title:
--   R: algebra Map quot mk
-- statement:
--   The R construction uses the algebra Map quot mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocA.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocA.lean#L22-L26

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

theorem ReciprocityTheory.AnForm.R.algebraMap_quot_mk (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) :
    algebraMap (MvPolynomial (Fin n) ℂ ⧸ K) (locRing K p) (Ideal.Quotient.mk K f) =
      algebraMap _ (locRing K p) f := by sorry

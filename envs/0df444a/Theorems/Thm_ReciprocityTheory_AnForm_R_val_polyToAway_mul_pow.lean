-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_val_polyToAway_mul_pow
-- name    : ReciprocityTheory.AnForm.R.val_polyToAway_mul_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:17:06.680827+00:00
-- url     : https://prove2.me/theorems/18348324-54ae-494e-b17b-5bd9353a69e5
-- title:
--   R: val poly To Away mul pow
-- statement:
--   The R construction uses the val poly To Away mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypC.lean#L113-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypC.lean#L113-L155

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)

theorem ReciprocityTheory.AnForm.R.val_polyToAway_mul_pow {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    letI := segreGraded hP
    (polyToAway hP p f).val * algebraMap _ (Localization.Away (segreW P p)) (segreW P p) ^ (∑ k, a k) =
      algebraMap _ (Localization.Away (segreW P p))
        (Ideal.Quotient.mk (segreIdeal P) (rename (chartUpd p) f)) := by sorry

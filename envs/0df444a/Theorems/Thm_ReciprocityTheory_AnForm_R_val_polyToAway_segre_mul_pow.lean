-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_val_polyToAway_segre_mul_pow
-- name    : ReciprocityTheory.AnForm.R.val_polyToAway_segre_mul_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:15:04.546698+00:00
-- url     : https://prove2.me/theorems/e331e6b4-e606-45dd-852f-ac64c7c89c63
-- title:
--   R: val poly To Away segre mul pow
-- statement:
--   The R construction uses the val poly To Away segre mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypC.lean#L157-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypC.lean#L157-L213

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

theorem ReciprocityTheory.AnForm.R.val_polyToAway_segre_mul_pow {g : MvPolynomial ((k : K) → ι k) ℂ} {d : ℕ}
    (hg : g.IsHomogeneous d) :
    letI := segreGraded hP
    (polyToAway hP p (segreMap g)).val * algebraMap _ (Localization.Away (segreW P p)) (segreW P p) ^ d =
      algebraMap _ (Localization.Away (segreW P p)) (Ideal.Quotient.mk (segreIdeal P) g) := by sorry

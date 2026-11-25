-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_away_eq_mk_of_val
-- name    : ReciprocityTheory.AnForm.R.away_eq_mk_of_val
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:48.299413+00:00
-- url     : https://prove2.me/theorems/f7923c57-387c-4712-a419-d3936cd9481e
-- title:
--   R: away eq mk of val
-- statement:
--   The R construction uses the away eq mk of val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypC.lean#L215-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypC.lean#L215-L228

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

theorem ReciprocityTheory.AnForm.R.away_eq_mk_of_val {N : ℕ} (n : MvPolynomial ((k : K) → ι k) ℂ) (hn : n.IsHomogeneous N)
    (a : letI := segreGraded hP; HomogeneousLocalization.Away (segreGrading P) (segreW P p))
    (h : letI := segreGraded hP; a.val * algebraMap _ (Localization.Away (segreW P p)) (segreW P p) ^ N =
      algebraMap _ _ (Ideal.Quotient.mk (segreIdeal P) n)) :
    letI := segreGraded hP
    a = HomogeneousLocalization.mk
      ({ deg := N
         num := ⟨Ideal.Quotient.mk _ n, n, (mem_homogeneousSubmodule N n).mpr hn, rfl⟩
         den := ⟨segreW P p ^ N, by simpa using SetLike.pow_mem_graded N (segreW_mem P p)⟩
         den_mem := ⟨N, rfl⟩ } :
        HomogeneousLocalization.NumDenSameDeg (segreGrading P) (Submonoid.powers (segreW P p))) := by sorry

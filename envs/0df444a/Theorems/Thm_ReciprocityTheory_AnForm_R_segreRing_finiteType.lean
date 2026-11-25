-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_segreRing_finiteType
-- name    : ReciprocityTheory.AnForm.R.segreRing_finiteType
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:56.623565+00:00
-- url     : https://prove2.me/theorems/7f43509a-e2f2-542c-a68c-104652a79d20
-- title:
--   R: segre Ring finite Type
-- statement:
--   The R construction uses the segre Ring finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L183-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L183-L194

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable [Nonempty K]

theorem ReciprocityTheory.AnForm.R.segreRing_finiteType {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    letI := segreGraded hP
    Algebra.FiniteType (segreGrading P 0) (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) := by sorry

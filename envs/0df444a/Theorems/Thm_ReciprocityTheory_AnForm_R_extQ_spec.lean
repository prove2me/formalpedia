-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_extQ_spec
-- name    : ReciprocityTheory.AnForm.R.extQ_spec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:55.439572+00:00
-- url     : https://prove2.me/theorems/aa5f5669-eed9-4084-b5f5-3665071f8a73
-- title:
--   R: ext Q spec
-- statement:
--   The R construction uses the ext Q spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRat.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRat.lean#L13-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IntegerToRational
variable {σ : Type} [Fintype σ]

theorem ReciprocityTheory.AnForm.R.extQ_spec (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ P → m = 0) :
    (extQ P).IsPrime ∧ (extQ P).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P ∧
      ringKrullDim (MvPolynomial σ ℚ ⧸ extQ P) + 1 = ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by sorry

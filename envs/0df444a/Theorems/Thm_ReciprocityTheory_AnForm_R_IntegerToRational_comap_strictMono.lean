-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_comap_strictMono
-- name    : ReciprocityTheory.AnForm.R.IntegerToRational.comap_strictMono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:07.485596+00:00
-- url     : https://prove2.me/theorems/60a75332-7787-4125-b957-3b272817a9ea
-- title:
--   Integer To Rational: comap strict Mono
-- statement:
--   The Integer To Rational construction uses the comap strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L46-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem ReciprocityTheory.AnForm.R.IntegerToRational.comap_strictMono :
    StrictMono (fun Q : Ideal (MvPolynomial σ ℚ) => Q.comap (MvPolynomial.map (Int.castRingHom ℚ))) := by sorry

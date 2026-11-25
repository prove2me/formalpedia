-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_quotientMap_bijective_of_loc
-- name    : ReciprocityTheory.ChartRestriction.G.I2.quotientMap_bijective_of_loc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:29:51.741064+00:00
-- url     : https://prove2.me/theorems/cda56706-f561-55bf-89e5-26b203356a31
-- title:
--   I2: quotient Map bijective of loc
-- statement:
--   The I2 construction uses the quotient Map bijective of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RCurveAlg.lean#L12-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RCurveAlg.lean#L12-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCurveAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2

theorem ReciprocityTheory.ChartRestriction.G.I2.quotientMap_bijective_of_loc {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (h : A) (K : Ideal A) (hK : h - 1 ∈ K)
    (hB : ∀ b : B, ∃ m : ℕ, ∃ a : A, algebraMap A B (h ^ m) * b = algebraMap A B a)
    (hinj : Function.Injective (algebraMap A B)) :
    Function.Bijective (Ideal.quotientMap (K.map (algebraMap A B)) (algebraMap A B)
      Ideal.le_comap_map) := by sorry

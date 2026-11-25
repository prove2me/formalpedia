-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_eQ_lt
-- name    : ReciprocityTheory.AnForm.R.IntegerToRational.eQ_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:29.260016+00:00
-- url     : https://prove2.me/theorems/c56df7ba-62d8-4161-9979-911461038bde
-- title:
--   Integer To Rational: e Q lt
-- statement:
--   The Integer To Rational construction uses the e Q lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatB.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatB.lean#L13-L27

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatB
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

theorem ReciprocityTheory.AnForm.R.IntegerToRational.eQ_lt {x y : PrimeSpectrum (MvPolynomial σ ℤ)} (hx : ChZero x.asIdeal)
    (hy : ChZero y.asIdeal) (hxy : x < y) : eQ x hx < eQ y hy := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isDomain_of_isRegularLocalRing
-- name    : ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:57.59521+00:00
-- url     : https://prove2.me/theorems/4ba294c5-64fd-4afb-ad71-6faa51988a54
-- title:
--   R: is Domain of is Regular Local Ring
-- statement:
--   The R construction uses the is Domain of is Regular Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/RegDom.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/RegDom.lean#L10-L11

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open IsLocalRing
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing [IsRegularLocalRing R] : IsDomain R := by sorry

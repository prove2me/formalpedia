-- Prove2me | Theorems.Thm_ReciprocityTheory_UG_AdeleIntA_isInt_add
-- name    : ReciprocityTheory.UG.AdeleIntA.isInt_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:20.264103+00:00
-- url     : https://prove2.me/theorems/ff242220-b35a-4e30-91f3-4cbe1a5fea65
-- title:
--   Adele Int A: is Int add
-- statement:
--   The Adele Int A construction uses the is Int add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdeleApproximation/AdeleIntA.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdeleApproximation/AdeleIntA.lean#L15-L16

import Mathlib
import Definitions.Def_ReciprocityTheory_AdeleApproximation_AdeleIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain WithZero
open ReciprocityTheory ReciprocityTheory.UG ReciprocityTheory.UG.AdeleIntA
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem ReciprocityTheory.UG.AdeleIntA.isInt_add {x y : FiniteAdeleRing R K} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) := by sorry

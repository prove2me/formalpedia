-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lib_AdeleIntA_isInt_add
-- name    : ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.isInt_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:19:58.064609+00:00
-- url     : https://prove2.me/theorems/a0688bd8-56fe-44d6-b716-678e4e550935
-- title:
--   Adele Int A: is Int add
-- statement:
--   The Adele Int A construction uses the is Int add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/AdeleApproximation/AdeleIntA.lean#L193-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/AdeleApproximation/AdeleIntA.lean#L193-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lib ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.isInt_add {a b : FiniteAdeleRing R K} (ha : IsInt a) (hb : IsInt b) : IsInt (a + b) := by sorry

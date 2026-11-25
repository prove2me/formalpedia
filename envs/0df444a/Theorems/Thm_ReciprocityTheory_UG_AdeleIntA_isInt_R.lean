-- Prove2me | Theorems.Thm_ReciprocityTheory_UG_AdeleIntA_isInt_R
-- name    : ReciprocityTheory.UG.AdeleIntA.isInt_R
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:15.91768+00:00
-- url     : https://prove2.me/theorems/8394e30a-2279-43d3-bfd9-cf529c3b3d66
-- title:
--   Adele Int A: is Int R
-- statement:
--   The Adele Int A construction uses the is Int R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdeleApproximation/AdeleIntA.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdeleApproximation/AdeleIntA.lean#L27-L32

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

theorem ReciprocityTheory.UG.AdeleIntA.isInt_R (r : R) : IsInt (algebraMap K (FiniteAdeleRing R K) (algebraMap R K r)) := by sorry

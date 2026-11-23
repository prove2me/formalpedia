-- Prove2me | Theorems.Thm_ReciprocityTheory_UG_AdeleIntA_val_le_one_of_mem
-- name    : ReciprocityTheory.UG.AdeleIntA.val_le_one_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:17.422086+00:00
-- url     : https://prove2.me/theorems/f228d75b-c06a-40ee-9bad-3f0fde78ab5d
-- title:
--   Adele Int A: val le one of mem
-- statement:
--   The Adele Int A construction uses the val le one of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdeleApproximation/AdeleIntA.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdeleApproximation/AdeleIntA.lean#L34-L35

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

theorem ReciprocityTheory.UG.AdeleIntA.val_le_one_of_mem {v : HeightOneSpectrum R} {x : v.adicCompletion K} (h : x ∈ v.adicCompletionIntegers K) :
    Valued.v x ≤ 1 := by sorry

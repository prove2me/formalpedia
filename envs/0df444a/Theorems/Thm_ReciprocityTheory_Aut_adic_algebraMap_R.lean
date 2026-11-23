-- Prove2me | Theorems.Thm_ReciprocityTheory_Aut_adic_algebraMap_R
-- name    : ReciprocityTheory.Aut.adic_algebraMap_R
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:34.232904+00:00
-- url     : https://prove2.me/theorems/21a575fb-9cd7-4bd3-a0f3-2e0a4daeebc1
-- title:
--   Aut: adic algebra Map R
-- statement:
--   The Aut construction uses the adic algebra Map R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/PlaceA.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/PlaceA.lean#L18-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Aut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem ReciprocityTheory.Aut.adic_algebraMap_R (a : R) :
    algebraMap R (v.adicCompletion K) a = algebraMap K (v.adicCompletion K) (algebraMap R K a) := by sorry

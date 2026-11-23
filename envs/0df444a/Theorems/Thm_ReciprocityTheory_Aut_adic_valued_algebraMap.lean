-- Prove2me | Theorems.Thm_ReciprocityTheory_Aut_adic_valued_algebraMap
-- name    : ReciprocityTheory.Aut.adic_valued_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:23.466498+00:00
-- url     : https://prove2.me/theorems/b0314acc-d2b9-42bf-ad79-5c32b24c85d7
-- title:
--   Aut: adic valued algebra Map
-- statement:
--   The Aut construction uses the adic valued algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/PlaceA.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/PlaceA.lean#L14-L16

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

theorem ReciprocityTheory.Aut.adic_valued_algebraMap (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k := by sorry

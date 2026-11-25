-- Prove2me | Theorems.Thm_ReciprocityTheory_Aut_adic_le_one_of_poly
-- name    : ReciprocityTheory.Aut.adic_le_one_of_poly
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:26.321141+00:00
-- url     : https://prove2.me/theorems/4423eb62-53e6-4927-9372-1e09aff0830c
-- title:
--   Aut: adic le one of poly
-- statement:
--   The Aut construction uses the adic le one of poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/PlaceA.lean#L95-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/PlaceA.lean#L95-L102

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

theorem ReciprocityTheory.Aut.adic_le_one_of_poly {x : v.adicCompletion K} (p : Polynomial ℤ) (hm : p.Monic)
    (hp : p.eval₂ (Int.castRingHom _) x = 0) : Valued.v x ≤ 1 := by sorry

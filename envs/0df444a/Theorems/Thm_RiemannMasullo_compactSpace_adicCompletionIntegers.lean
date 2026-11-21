-- Prove2me | Theorems.Thm_RiemannMasullo_compactSpace_adicCompletionIntegers
-- name    : RiemannMasullo.compactSpace_adicCompletionIntegers
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:39:32.489274+00:00
-- url     : https://prove2.me/theorems/11862d30-79cc-434f-a64c-bf829a3f46c6
-- title:
--   Compactness of the integers in the adic completion
-- statement:
--   The valuation ring of the completion at a height-one prime of a Dedekind domain with finite quotients is compact.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/NumberTheory/NumberField/Completion/FinitePlace.lean#L77-L84

import Mathlib

open Filter IsDedekindDomain IsLocalRing Topology
open scoped WithZero
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  [Field K] [Algebra R K] [IsFractionRing R K]

namespace RiemannMasullo

theorem compactSpace_adicCompletionIntegers (v : HeightOneSpectrum R) :
    CompactSpace (v.adicCompletionIntegers K) := by sorry

end RiemannMasullo

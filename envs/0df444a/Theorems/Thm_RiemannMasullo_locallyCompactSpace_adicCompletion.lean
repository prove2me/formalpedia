-- Prove2me | Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
-- name    : RiemannMasullo.locallyCompactSpace_adicCompletion
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:39:30.717181+00:00
-- url     : https://prove2.me/theorems/c7a24bb5-0bf8-47a9-8d90-af2229af2bfb
-- title:
--   Local compactness of the adic completion
-- statement:
--   Under the finite-quotient hypothesis on the Dedekind domain, its height-one adic completion is locally compact.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/NumberTheory/NumberField/Completion/FinitePlace.lean#L70-L73

import Mathlib

open Filter IsDedekindDomain IsLocalRing Topology
open scoped WithZero
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  [Field K] [Algebra R K] [IsFractionRing R K]

namespace RiemannMasullo

theorem locallyCompactSpace_adicCompletion (v : HeightOneSpectrum R) :
    LocallyCompactSpace (v.adicCompletion K) := by sorry

end RiemannMasullo

-- Prove2me | Theorems.Thm_RiemannMasullo_properSpace_adicCompletion
-- name    : RiemannMasullo.properSpace_adicCompletion
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:46:14.43991+00:00
-- url     : https://prove2.me/theorems/e08959e4-8398-482e-b323-02b80ca14ac1
-- title:
--   Properness of the adic completion
-- statement:
--   The completion of the fraction field of a Dedekind domain at a height-one prime is a proper metric space when the domain has finite quotients.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/NumberTheory/NumberField/Completion/FinitePlace.lean#L62-L66

import Mathlib
import Definitions.Def_RiemannMasullo_AdicCompletionNorm
open scoped RiemannMasullo.AdicCompletionNorm
open Valued.integer

open Filter IsDedekindDomain IsLocalRing Topology
open scoped WithZero
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  [Field K] [Algebra R K] [IsFractionRing R K]

namespace RiemannMasullo

theorem properSpace_adicCompletion (v : HeightOneSpectrum R) :
    ProperSpace (v.adicCompletion K) := by sorry

end RiemannMasullo

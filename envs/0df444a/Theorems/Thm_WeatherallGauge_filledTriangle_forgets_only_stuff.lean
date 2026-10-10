-- Prove2me | Theorems.Thm_WeatherallGauge_filledTriangle_forgets_only_stuff
-- name    : WeatherallGauge.filledTriangle_forgets_only_stuff
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T21:22:27.254906+00:00
-- url     : https://prove2.me/theorems/918a6dcd-d7a5-4f1a-89e9-0da676d9bd29
-- title:
--   Filled triangle: A ↦ δA forgets only stuff
-- statement:
--   On `filledTriangle` (`circle3` plus one face bounded by all three edges) with $\mathbb Z$ coefficients, the functor `PotG` $\to$ `Fld` is full and essentially surjective but not faithful.
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), §3, p. 7 (stuff/structure/property) and §4, p. 11, fn. 15, discrete example

import Mathlib
import Definitions.Def_WeatherallGauge_defs

open CategoryTheory

namespace WeatherallGauge

/-- On the filled triangle with `ℤ` coefficients the field-strength functor is full and
essentially surjective but not faithful: constant gauge transformations are non-trivial arrows
sent to identities (it "forgets only stuff"). -/
theorem filledTriangle_forgets_only_stuff :
    (fieldStrength (X := filledTriangle) (K := ℤ)).Full ∧
    (fieldStrength (X := filledTriangle) (K := ℤ)).EssSurj ∧
    ¬ (fieldStrength (X := filledTriangle) (K := ℤ)).Faithful := by sorry

end WeatherallGauge

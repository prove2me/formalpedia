-- Prove2me | Theorems.Thm_WeatherallGauge_aharonov_bohm
-- name    : WeatherallGauge.aharonov_bohm
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T21:21:39.602983+00:00
-- url     : https://prove2.me/theorems/a5953e6b-832c-4b46-9bcd-cd716d30101d
-- title:
--   Aharonov–Bohm: on a circle A ↦ δA is not full
-- statement:
--   On `circle3` (three vertices, edges $e:e\to e+1$ mod 3, no faces) with $\mathbb Z$ coefficients, the potential $A=\mathbf 1_{e=0}$ satisfies $\delta^1A=\delta^1 0$ (trivially: no faces), there is no gauge arrow $A\to0$ in `PotG`, and the field-strength functor `PotG` $\to$ `Fld` is not full.
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), fn. 9 (topology set aside), discrete counterexample

import Mathlib
import Definitions.Def_WeatherallGauge_defs

open CategoryTheory

namespace WeatherallGauge

/-- Aharonov–Bohm on the circle `circle3` with `ℤ` coefficients: the potential that is `1` on
edge `0` has the same field strength as the zero potential (trivially, as `circle3`
has no faces), yet no gauge transformation relates
them; hence the field-strength functor is not full. -/
theorem aharonov_bohm :
    delta1 (Pi.single 0 1 : C1 circle3 ℤ) = delta1 0 ∧
    IsEmpty ((⟨Pi.single 0 1⟩ : PotG circle3 ℤ) ⟶ ⟨0⟩) ∧
    ¬ (fieldStrength (X := circle3) (K := ℤ)).Full := by sorry

end WeatherallGauge

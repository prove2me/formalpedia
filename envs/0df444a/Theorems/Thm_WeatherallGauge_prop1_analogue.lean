-- Prove2me | Theorems.Thm_WeatherallGauge_prop1_analogue
-- name    : WeatherallGauge.prop1_analogue
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T21:19:14.465557+00:00
-- url     : https://prove2.me/theorems/b403eecc-714d-4093-b782-e306275d8f73
-- title:
--   Prop. 1 analogue: without gauge arrows A ↦ δA forgets structure
-- statement:
--   Throughout, $X$ is a finite oriented 2-complex (cells indexed by `Fin`, integer incidence numbers with $\partial\partial=0$), $K$ an additive commutative group, $\delta^0:C^0\to C^1$, $\delta^1:C^1\to C^2$ the coboundaries; `PotG` has potentials as objects and gauge parameters $\lambda$ with $A+\delta^0\lambda=A'$ as arrows $A\to A'$; `Pot0` and `Fld` are discrete; the functors send $A\mapsto\delta^1A$. If $\delta^0\lambda\ne0$ for some $\lambda$, the functor `Pot0` $\to$ `Fld` is faithful, not full, and essentially surjective iff every 2-cochain is a coboundary ($H^2=0$).
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), §4, p. 8, Proposition 1

import Mathlib
import Definitions.Def_WeatherallGauge_defs

open CategoryTheory

namespace WeatherallGauge

/-- Analogue of Weatherall (2016), Prop. 1: without gauge arrows, `A ↦ δA` is faithful, is not
full as soon as the coboundary `δ⁰` is not the zero map, and is essentially surjective iff
`H² = 0`. -/
theorem prop1_analogue (X : CellComplex2) (K : Type) [AddCommGroup K]
    (h : ∃ lam : C0 X K, delta0 lam ≠ 0) :
    (fieldStrength0 (X := X) (K := K)).Faithful ∧ ¬ (fieldStrength0 (X := X) (K := K)).Full ∧
    ((fieldStrength0 (X := X) (K := K)).EssSurj ↔ H2Vanishes X K) := by sorry

end WeatherallGauge

-- Prove2me | Theorems.Thm_WeatherallGauge_essSurj_iff
-- name    : WeatherallGauge.essSurj_iff
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T21:21:17.246448+00:00
-- url     : https://prove2.me/theorems/513427d5-6cab-49dd-9f4e-d8004227ebef
-- title:
--   Essentially surjective iff H² = 0
-- statement:
--   Throughout, $X$ is a finite oriented 2-complex (cells indexed by `Fin`, integer incidence numbers with $\partial\partial=0$), $K$ an additive commutative group, $\delta^0:C^0\to C^1$, $\delta^1:C^1\to C^2$ the coboundaries; `PotG` has potentials as objects and gauge parameters $\lambda$ with $A+\delta^0\lambda=A'$ as arrows $A\to A'$; `Pot0` and `Fld` are discrete; the functors send $A\mapsto\delta^1A$. The functor `PotG` $\to$ `Fld` is essentially surjective iff every 2-cochain is $\delta^1A$ for some $A$.
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), §4, p. 11, fn. 15 (EM2 with gauge arrows), discrete analogue

import Mathlib
import Definitions.Def_WeatherallGauge_defs

open CategoryTheory

namespace WeatherallGauge

/-- The functor `A ↦ δA` on potentials with gauge arrows is essentially surjective iff
`H²(X;K) = 0`. -/
theorem essSurj_iff (X : CellComplex2) (K : Type) [AddCommGroup K] :
    fieldStrength (X := X) (K := K).EssSurj ↔ H2Vanishes X K := by sorry

end WeatherallGauge

-- Prove2me | Theorems.Thm_WeatherallGauge_faithful_iff
-- name    : WeatherallGauge.faithful_iff
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T21:19:41.691114+00:00
-- url     : https://prove2.me/theorems/cb537c11-23f8-4652-8b77-1b2c717be7c5
-- title:
--   Faithful iff H⁰ = 0 (constant gauge transformations are stuff)
-- statement:
--   Throughout, $X$ is a finite oriented 2-complex (cells indexed by `Fin`, integer incidence numbers with $\partial\partial=0$), $K$ an additive commutative group, $\delta^0:C^0\to C^1$, $\delta^1:C^1\to C^2$ the coboundaries; `PotG` has potentials as objects and gauge parameters $\lambda$ with $A+\delta^0\lambda=A'$ as arrows $A\to A'$; `Pot0` and `Fld` are discrete; the functors send $A\mapsto\delta^1A$. The functor `PotG` $\to$ `Fld` is faithful iff $\delta^0\lambda=0$ implies $\lambda=0$.
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), §4, p. 11, fn. 15 (EM2 with gauge arrows); matches Proposition 2 as corrected by the erratum (arXiv v2, p. 15)

import Mathlib
import Definitions.Def_WeatherallGauge_defs

open CategoryTheory

namespace WeatherallGauge

/-- The functor `A ↦ δA` on potentials with gauge arrows is faithful iff `H⁰(X;K) = 0`. -/
theorem faithful_iff (X : CellComplex2) (K : Type) [AddCommGroup K] :
    fieldStrength (X := X) (K := K).Faithful ↔ H0Vanishes X K := by sorry

end WeatherallGauge

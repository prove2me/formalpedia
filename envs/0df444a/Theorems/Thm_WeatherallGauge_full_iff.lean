-- Prove2me | Theorems.Thm_WeatherallGauge_full_iff
-- name    : WeatherallGauge.full_iff
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T21:20:27.255975+00:00
-- url     : https://prove2.me/theorems/3394ee09-a544-49c3-ad27-623f2ddd09f9
-- title:
--   Full iff H¹ = 0
-- statement:
--   Throughout, $X$ is a finite oriented 2-complex (cells indexed by `Fin`, integer incidence numbers with $\partial\partial=0$), $K$ an additive commutative group, $\delta^0:C^0\to C^1$, $\delta^1:C^1\to C^2$ the coboundaries; `PotG` has potentials as objects and gauge parameters $\lambda$ with $A+\delta^0\lambda=A'$ as arrows $A\to A'$; `Pot0` and `Fld` are discrete; the functors send $A\mapsto\delta^1A$. The functor `PotG` $\to$ `Fld` is full iff every 1-cochain $A$ with $\delta^1A=0$ is $\delta^0\lambda$ for some $\lambda$.
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), §4, p. 11, fn. 15 (EM2 with gauge arrows) and p. 4, fn. 9 (topology set aside), discrete analogue

import Mathlib
import Definitions.Def_WeatherallGauge_defs

open CategoryTheory

namespace WeatherallGauge

/-- The functor `A ↦ δA` on potentials with gauge arrows is full iff `H¹(X;K) = 0`. -/
theorem full_iff (X : CellComplex2) (K : Type) [AddCommGroup K] :
    fieldStrength (X := X) (K := K).Full ↔ H1Vanishes X K := by sorry

end WeatherallGauge

-- Prove2me | Theorems.Thm_WeatherallGauge_classification
-- name    : WeatherallGauge.classification
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T21:24:35.071641+00:00
-- url     : https://prove2.me/theorems/99da5ee4-bc53-4ef5-9081-4ece28ddb878
-- title:
--   Cohomological classification of the field-strength functor
-- statement:
--   Throughout, $X$ is a finite oriented 2-complex (cells indexed by `Fin`, integer incidence numbers with $\partial\partial=0$), $K$ an additive commutative group, $\delta^0:C^0\to C^1$, $\delta^1:C^1\to C^2$ the coboundaries; `PotG` has potentials as objects and gauge parameters $\lambda$ with $A+\delta^0\lambda=A'$ as arrows $A\to A'$; `Pot0` and `Fld` are discrete; the functors send $A\mapsto\delta^1A$. For every $X$ and $K$: `PotG` $\to$ `Fld` is faithful iff $H^0=0$, full iff $H^1=0$, and essentially surjective iff $H^2=0$, with $H^i=0$ in the elementary forms of the definitions.
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), §3 p. 7 and §4 pp. 8–11 (Proposition 1, fn. 9, fn. 15; Proposition 2 as corrected by the erratum, p. 15), discrete analogue

import Mathlib
import Definitions.Def_WeatherallGauge_defs

open CategoryTheory

namespace WeatherallGauge

/-- Main goal. For the field-strength functor `A ↦ δA` from potentials with gauge arrows to
field strengths on a finite 2-complex `X` with coefficients `K`: it is faithful iff `H⁰ = 0`,
full iff `H¹ = 0`, and essentially surjective iff `H² = 0`. -/
theorem classification (X : CellComplex2) (K : Type) [AddCommGroup K] :
    (fieldStrength (X := X) (K := K).Faithful ↔ H0Vanishes X K) ∧ (fieldStrength (X := X) (K := K).Full ↔ H1Vanishes X K) ∧
    (fieldStrength (X := X) (K := K).EssSurj ↔ H2Vanishes X K) := by sorry

end WeatherallGauge

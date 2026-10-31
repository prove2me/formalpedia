-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P26_generalizedDimensions
-- name    : QAlgorithms.Papers.Independent.Intake100.P26.generalizedDimensions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:22:03.479591+00:00
-- url     : https://prove2.me/theorems/3e7318ee-f6e8-4124-a7bf-accc0e32685f
-- title:
--   Generalized weight dimensions are constant on components
-- statement:
--   Let $R$ be a finite reduced irreducible crystallographic root system of positive rank, with a fixed positive system and simple roots $\alpha_i$, Weyl group $W$, and full weight lattice $P$. Fix $q\in\mathbb C^\times$ which is not a root of unity. Write $\widetilde H$ for its affine Hecke algebra with $T_i^2=(q-q^{-1})T_i+1$ and the Bernstein relation with denominator $1-X^{-\alpha_i}$ interpreted as a Laurent-polynomial divided difference. Let $T=\operatorname{Hom}(P,\mathbb C^\times)$, with $(wt)(X^\lambda)=t(X^{w^{-1}\lambda})$. All modules below are finite dimensional complex left modules. Irreducible modules are nonzero.
--
--   Let $M$ be such a module. The calibration graph on an orbit $Wt$ has distinct vertices $b$ and $s_i b$ joined when $b(X^{\alpha_i})\notin\{q^2,q^{-2}\}$. If $b$ and $c$ belong to the same connected component, then
--   $$\dim_{\mathbb C}M_b^{\rm gen}=\dim_{\mathbb C}M_c^{\rm gen}.$$
--   The vertices need not occur in the support of $M$; both dimensions may be zero. This gives a module-independent constraint on weight multiplicities along calibration edges.
-- source:
--   Calibrated representations of affine Hecke algebras, arXiv:math/0401323v2, PDF p. 10, Proposition 2.12

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P26

open scoped BigOperators

variable {D : Datum} {V U : Type*}

variable [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

/-- Proposition 2.12, PDF p.10: arbitrary vertices, including absent weights. -/
theorem generalizedDimensions (D : Datum) (q : ℂ) (hq : GoodParameter q)
    (A : HeckeGenerators D V) [FiniteDimensional ℂ V] (hA : Relations q A)
    (t u : Torus D) (hpath : Connected D q t u) :
    Module.finrank ℂ (genSpace A t) = Module.finrank ℂ (genSpace A u) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P26

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P26_weightMultiplicityOne
-- name    : QAlgorithms.Papers.Independent.Intake100.P26.weightMultiplicityOne
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:25:54.221004+00:00
-- url     : https://prove2.me/theorems/93e9fed1-b3a3-475a-ba94-2133f6b6436a
-- title:
--   Regularity and multiplicity one of calibrated irreducible weights
-- statement:
--   Let $R$ be a finite reduced irreducible crystallographic root system of positive rank, with a fixed positive system and simple roots $\alpha_i$, Weyl group $W$, and full weight lattice $P$. Fix $q\in\mathbb C^\times$ which is not a root of unity. Write $\widetilde H$ for its affine Hecke algebra with $T_i^2=(q-q^{-1})T_i+1$ and the Bernstein relation with denominator $1-X^{-\alpha_i}$ interpreted as a Laurent-polynomial divided difference. Let $T=\operatorname{Hom}(P,\mathbb C^\times)$, with $(wt)(X^\lambda)=t(X^{w^{-1}\lambda})$. All modules below are finite dimensional complex left modules. Irreducible modules are nonzero.
--
--   Let $M$ be irreducible and calibrated. Then every occurring ordinary weight $t$ satisfies
--   $$t(X^{\alpha_i})\ne1\quad\text{for every simple root }\alpha_i,\qquad \dim_{\mathbb C}M_t=1.$$
--   Both simple-root regularity and multiplicity one are conclusions. They make the coefficient formulas of Proposition 4.1 applicable to calibrated irreducible modules.
-- source:
--   Calibrated representations of affine Hecke algebras, arXiv:math/0401323v2, PDF p. 16, Proposition 4.2(a)–(b)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P26

open scoped BigOperators

variable {D : Datum} {V U : Type*}

variable [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

/-- Proposition 4.2(a)--(b), PDF pp.16--17. Both regularity and multiplicity
one are conclusions; neither is assumed. -/
theorem weightMultiplicityOne (D : Datum) (q : ℂ) (hq : GoodParameter q)
    (A : HeckeGenerators D V) [FiniteDimensional ℂ V] (hA : Relations q A)
    (hirr : HeckeIrreducible A) (hcal : Calibrated A) :
    ∀ t, weightSpace A t ≠ ⊥ →
      (∀ i, torusCharacterEval t (simpleRootWeight D i) ≠ 1) ∧
      Module.finrank ℂ (weightSpace A t) = 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P26

end

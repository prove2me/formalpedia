-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P26_supportUnion
-- name    : QAlgorithms.Papers.Independent.Intake100.P26.supportUnion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:22:50.682987+00:00
-- url     : https://prove2.me/theorems/d35456c3-3935-493e-a475-77ea2b239793
-- title:
--   Irreducible support is a union of calibration components
-- statement:
--   Let $R$ be a finite reduced irreducible crystallographic root system of positive rank, with a fixed positive system and simple roots $\alpha_i$, Weyl group $W$, and full weight lattice $P$. Fix $q\in\mathbb C^\times$ which is not a root of unity. Write $\widetilde H$ for its affine Hecke algebra with $T_i^2=(q-q^{-1})T_i+1$ and the Bernstein relation with denominator $1-X^{-\alpha_i}$ interpreted as a Laurent-polynomial divided difference. Let $T=\operatorname{Hom}(P,\mathbb C^\times)$, with $(wt)(X^\lambda)=t(X^{w^{-1}\lambda})$. All modules below are finite dimensional complex left modules. Irreducible modules are nonzero.
--
--   Let $M$ be irreducible with central character $Wt$. Here central character means that every $W$-invariant Laurent polynomial acts on $M$ by its evaluation at $t$. Let $\operatorname{supp}(M)=\{b:M_b^{\rm gen}\ne0\}$, and let $\Gamma(t)$ be the calibration graph on $Wt$, whose edges join distinct $b,s_i b$ when $b(X^{\alpha_i})\ne q^{\pm2}$. Then
--   $$\operatorname{supp}(M)\subseteq Wt,\qquad b\in\operatorname{supp}(M),\ c\sim_{\Gamma(t)}b\ \Longrightarrow\ c\in\operatorname{supp}(M).$$
--   Equivalently, the support is a union of connected components of $\Gamma(t)$. This conclusion does not assert that the support is a single component.
-- source:
--   Calibrated representations of affine Hecke algebras, arXiv:math/0401323v2, PDF p. 10, Corollary 2.13

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P26

open scoped BigOperators

variable {D : Datum} {V U : Type*}

variable [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

/-- Corollary 2.13, PDF p.10. Inclusion in the central-character orbit together
with closure under connectedness says exactly that support is a union of components. -/
theorem supportUnion (D : Datum) (q : ℂ) (hq : GoodParameter q)
    (A : HeckeGenerators D V) [FiniteDimensional ℂ V] (hA : Relations q A)
    (hirr : HeckeIrreducible A) (t : Torus D) (hcentral : CentralCharacter A t) :
    generalizedSupport A ⊆ characterOrbit D t ∧
      ∀ u ∈ generalizedSupport A, ∀ v, Connected D q u v → v ∈ generalizedSupport A := by sorry

end QAlgorithms.Papers.Independent.Intake100.P26

end

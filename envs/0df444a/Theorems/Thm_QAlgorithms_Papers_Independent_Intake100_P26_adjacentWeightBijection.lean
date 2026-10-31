-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P26_adjacentWeightBijection
-- name    : QAlgorithms.Papers.Independent.Intake100.P26.adjacentWeightBijection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:26:31.443106+00:00
-- url     : https://prove2.me/theorems/9b57bd1c-3dd2-496d-9992-e4cf462e411c
-- title:
--   Tau is bijective between adjacent occurring weights
-- statement:
--   Let $R$ be a finite reduced irreducible crystallographic root system of positive rank, with a fixed positive system and simple roots $\alpha_i$, Weyl group $W$, and full weight lattice $P$. Fix $q\in\mathbb C^\times$ which is not a root of unity. Write $\widetilde H$ for its affine Hecke algebra with $T_i^2=(q-q^{-1})T_i+1$ and the Bernstein relation with denominator $1-X^{-\alpha_i}$ interpreted as a Laurent-polynomial divided difference. Let $T=\operatorname{Hom}(P,\mathbb C^\times)$, with $(wt)(X^\lambda)=t(X^{w^{-1}\lambda})$. All modules below are finite dimensional complex left modules. Irreducible modules are nonzero.
--
--   Let $M$ be irreducible and calibrated, let $t\in T$, and let $\alpha_i$ be simple. Suppose both $M_t$ and $M_{s_i t}$ are nonzero. Then the local operator satisfies
--   $$\tau_i:M_t\longrightarrow M_{s_i t}\quad\text{is a bijection}.$$
--   Here $\tau_i=T_i-(q-q^{-1})(1-X^{-\alpha_i})^{-1}$ on the incoming weight space. Its definedness follows from the theorem's hypotheses; no extra exclusion of $q^{\pm2}$ is assumed. This gives invertibility from occurrence and calibrated irreducibility alone.
-- source:
--   Calibrated representations of affine Hecke algebras, arXiv:math/0401323v2, PDF p. 17, Proposition 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P26

open scoped BigOperators

variable {D : Datum} {V U : Type*}

variable [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

/-- Proposition 4.3, PDF pp.17--18. No q^+-2 exclusion or regularity
assumption is added: those facts follow from the source's hypotheses. -/
theorem adjacentWeightBijection (D : Datum) (q : ℂ) (hq : GoodParameter q)
    (A : HeckeGenerators D V) [FiniteDimensional ℂ V] (hA : Relations q A)
    (hirr : HeckeIrreducible A) (hcal : Calibrated A) (t : Torus D) (i : Fin D.rank)
    (ht : weightSpace A t ≠ ⊥) (hs : weightSpace A (weylCharacter D (simple D i) t) ≠ ⊥) :
    Set.BijOn (localIntertwiner q A t i) (weightSpace A t)
      (weightSpace A (weylCharacter D (simple D i) t)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P26

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P22_cartan_toralComplement
-- name    : QAlgorithms.Papers.Independent.Renew46.P22.cartan_toralComplement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:35:41.457669+00:00
-- url     : https://prove2.me/theorems/6896b4d3-c508-4d09-91d5-fcd35a8eefe2
-- title:
--   Every Cartan subalgebra supplies a toral complement
-- statement:
--   Let $F$ be a field of characteristic zero and let $K$ be its specified algebraic closure, with its embedding of $F$. All groups below are geometric subgroups of $\mathrm{GL}_n(K)$, and all closures are relative Zariski closures in that group.
--
--   Let $\mathfrak g\subseteq\mathfrak{gl}_n(F)$ be the Lie algebra of a connected algebraic group defined over $F$. Write $\mathfrak s=\operatorname{rad}(\mathfrak g)$ and let $\mathfrak n$ be its largest ideal consisting of nilpotent ambient matrices. Assume the section’s starting structure: an abelian matrix-semisimple subalgebra $\mathfrak d\subseteq\mathfrak s$ satisfies $\mathfrak s=\mathfrak d\ltimes\mathfrak n$, and $\mathfrak n$ is exactly the set of nilpotent matrices in $\mathfrak s$. For every Cartan subalgebra $\mathfrak h^\ast$ of $\mathfrak s$, there exists an abelian matrix-semisimple subalgebra $\mathfrak d^\ast\subseteq\mathfrak s$ such that
--
--   $$\mathfrak s=\mathfrak d^\ast\ltimes\mathfrak n,\qquad \mathfrak h^\ast=C_{\mathfrak s}(\mathfrak d^\ast)=\mathfrak d^\ast+C_{\mathfrak n}(\mathfrak d^\ast).$$
--
--   This associates a toral complement to each chosen Cartan subalgebra. It does not assert that the new complement centralizes a previously fixed Levi factor.
-- source:
--   Constructing algebraic groups from their Lie algebras, arXiv:math/0612557v1, PDF p. 8, Lemma 10

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P22

open scoped BigOperators Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing

section LieStructure

variable {F K : Type*} [Field F] [hchar : CharZero F] [Field K] [Algebra F K] [hclosure : IsAlgClosure F K]

variable {n : ℕ}

section

include hchar hclosure

/-- Lemma 10, PDF pp.8–9: every Cartan subalgebra has a toral complement; no compatibility
with a previously fixed Levi factor is claimed for the new complement. -/
theorem cartan_toralComplement (g : LieSubalgebra F (Matrix (Fin n) (Fin n) F))
    (d : LieSubalgebra F g) (ctx : SolvableContext (K := K) g d)
    (h : LieSubalgebra F g) (hh : IsCartanInRadical g h) :
    ∃ dnew : LieSubalgebra F g, ToralComplement g dnew ∧
      h = centralizerWithin (LieAlgebra.radical F g).toLieSubalgebra dnew ∧
      h.toSubmodule = dnew.toSubmodule ⊔
        (centralizerWithin (matrixNilpotentIdeal g).toLieSubalgebra dnew).toSubmodule := by sorry

end

end LieStructure

end QAlgorithms.Papers.Independent.Renew46.P22

end

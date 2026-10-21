-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P22_toralCentralizer_isCartan
-- name    : QAlgorithms.Papers.Independent.Renew46.P22.toralCentralizer_isCartan
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:35:07.11232+00:00
-- url     : https://prove2.me/theorems/9b0cf1e3-34b5-4a80-ad53-6835969dd28a
-- title:
--   The centralizer of the toral complement is Cartan
-- statement:
--   Let $F$ be a field of characteristic zero and let $K$ be its specified algebraic closure, with its embedding of $F$. All groups below are geometric subgroups of $\mathrm{GL}_n(K)$, and all closures are relative Zariski closures in that group.
--
--   Let $\mathfrak g\subseteq\mathfrak{gl}_n(F)$ be the Lie algebra of a connected algebraic group defined over $F$. Write $\mathfrak s=\operatorname{rad}(\mathfrak g)$ and let $\mathfrak n$ be its largest ideal consisting of nilpotent ambient matrices. Assume the section’s starting structure: an abelian matrix-semisimple subalgebra $\mathfrak d\subseteq\mathfrak s$ satisfies $\mathfrak s=\mathfrak d\ltimes\mathfrak n$, and $\mathfrak n$ is exactly the set of nilpotent matrices in $\mathfrak s$. Define $\mathfrak h=C_{\mathfrak s}(\mathfrak d)$. Then $\mathfrak h$ is a Cartan subalgebra of $\mathfrak s$, meaning nilpotent and self-normalizing in $\mathfrak s$, and
--
--   $$\mathfrak h=\mathfrak d+C_{\mathfrak n}(\mathfrak d).$$
--
--   The sum is a sum of vector subspaces. This identifies the Cartan subalgebra attached to the initial toral complement.
-- source:
--   Constructing algebraic groups from their Lie algebras, arXiv:math/0612557v1, PDF p. 8, Lemma 9

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

/-- Lemma 9, PDF p.8: h is constructed as the centralizer; the displayed sum is linear. -/
theorem toralCentralizer_isCartan (g : LieSubalgebra F (Matrix (Fin n) (Fin n) F))
    (d : LieSubalgebra F g) (ctx : SolvableContext (K := K) g d) :
    IsCartanInRadical g (centralizerWithin (LieAlgebra.radical F g).toLieSubalgebra d) ∧
    (centralizerWithin (LieAlgebra.radical F g).toLieSubalgebra d).toSubmodule =
      d.toSubmodule ⊔ (centralizerWithin (matrixNilpotentIdeal g).toLieSubalgebra d).toSubmodule := by sorry

end

end LieStructure

end QAlgorithms.Papers.Independent.Renew46.P22

end

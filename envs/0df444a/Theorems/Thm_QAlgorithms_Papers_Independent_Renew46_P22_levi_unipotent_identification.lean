-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P22_levi_unipotent_identification
-- name    : QAlgorithms.Papers.Independent.Renew46.P22.levi_unipotent_identification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:34:35.40225+00:00
-- url     : https://prove2.me/theorems/2753b2b1-8df0-471c-a24b-64eb9b94210f
-- title:
--   Compatible Lie summands reconstruct the Levi subgroup and unipotent radical
-- statement:
--   Let $F$ be a field of characteristic zero and let $K$ be its specified algebraic closure, with its embedding of $F$. All groups below are geometric subgroups of $\mathrm{GL}_n(K)$, and all closures are relative Zariski closures in that group.
--
--   Let $\mathfrak g\subseteq\mathfrak{gl}_n(F)$ be the Lie algebra of a connected algebraic group defined over $F$. Write $\mathfrak s=\operatorname{rad}(\mathfrak g)$ and let $\mathfrak n$ be its largest ideal consisting of nilpotent ambient matrices. Assume the section’s starting structure: an abelian matrix-semisimple subalgebra $\mathfrak d\subseteq\mathfrak s$ satisfies $\mathfrak s=\mathfrak d\ltimes\mathfrak n$, and $\mathfrak n$ is exactly the set of nilpotent matrices in $\mathfrak s$. Let $G$ be the corresponding connected $F$-defined algebraic group and let $\mathfrak l$ be a Levi subalgebra of $\mathfrak g$. Assume the section’s explicit compatibility $[\mathfrak l,\mathfrak d]=0$. Define $H$ and $U$ by the intrinsic algebraic hulls of $\mathfrak l+\mathfrak d$ and $\mathfrak n$, respectively. Then $H$ and $U$ are defined over $F$ and
--
--   $$\operatorname{Lie}_F(H)=\mathfrak l+\mathfrak d,\qquad \operatorname{Lie}_F(U)=\mathfrak n,\qquad G=H\ltimes U.$$
--
--   Moreover, $H$ is a maximal reductive subgroup of $G$, and $U$ is its unipotent radical, the largest connected normal unipotent algebraic subgroup. This identifies the groups corresponding to the compatible Lie summands.
-- source:
--   Constructing algebraic groups from their Lie algebras, arXiv:math/0612557v1, PDF p. 8, Unnumbered identification in §5

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

/-- Unnumbered identification, PDF p.8. Uses the explicitly compatible Levi factor and d.
Printed: "unique maximal unipotent subgroup". Changed: largest connected normal unipotent
subgroup. Why: the named unipotent radical requires normality; GL2 refutes the literal phrase.
This correction awaits independent moderation. -/
theorem levi_unipotent_identification (g : LieSubalgebra F (Matrix (Fin n) (Fin n) F))
    (d : LieSubalgebra F g) (ctx : SolvableContext (K := K) g d)
    (G : Subgroup (GeometricGL n K)) (hG : IsAlgebraicGroup G) (hF : DefinedOver F G)
    (hconn : IsZariskiConnected (G : Set (GeometricGL n K)))
    (hLie : tangentSet F G = (g : Set (Matrix (Fin n) (Fin n) F)))
    (l : LieSubalgebra F g) (hsemisimple : LieAlgebra.radical F l = ⊥)
    (hLevi : IsCompl l.toSubmodule (LieAlgebra.radical F g).toSubmodule)
    (hcompat : ∀ x : l, ∀ y : d, ⁅(x : g), (y : g)⁆ = 0) :
    let H := groupHull F K (ambientSubmodule g (l.toSubmodule ⊔ d.toSubmodule))
    let U := groupHull F K (ambientSubmodule g (matrixNilpotentIdeal g).toSubmodule)
    tangentSet F H = (ambientSubmodule g (l.toSubmodule ⊔ d.toSubmodule) : Set (Matrix (Fin n) (Fin n) F)) ∧
    tangentSet F U = (ambientSubmodule g (matrixNilpotentIdeal g).toSubmodule : Set (Matrix (Fin n) (Fin n) F)) ∧
    DefinedOver F H ∧ DefinedOver F U ∧
    IsMaximalReductiveWithin G H ∧ IsUnipotentRadical G U ∧ IsSemidirectProduct G H U := by sorry

end

end LieStructure

end QAlgorithms.Papers.Independent.Renew46.P22

end

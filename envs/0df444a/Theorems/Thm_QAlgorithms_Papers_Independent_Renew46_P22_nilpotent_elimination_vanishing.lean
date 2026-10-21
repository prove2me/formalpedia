-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P22_nilpotent_elimination_vanishing
-- name    : QAlgorithms.Papers.Independent.Renew46.P22.nilpotent_elimination_vanishing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:31:49.630318+00:00
-- url     : https://prove2.me/theorems/b8d25aec-2d0b-4284-8fd6-b87406738c67
-- title:
--   Nilpotent exponential elimination gives the entire vanishing ideal
-- statement:
--   Let $F$ be a field of characteristic zero and let $K$ be its specified algebraic closure, with its embedding of $F$. All groups below are geometric subgroups of $\mathrm{GL}_n(K)$, and all closures are relative Zariski closures in that group.
--
--   Let $\mathfrak N\subseteq\mathfrak{gl}_n(F)$ be a Lie subalgebra all of whose matrices are nilpotent, and let $N_1,\ldots,N_r$ be an $F$-basis. In $P=F[T_1,\ldots,T_r,x_{ij}]$ set $M=\exp(\sum_i T_i N_i)$, using its finite polynomial exponential, and $I=(x_{ij}-M_{ij})$. Let $G(\mathfrak N)$ be the connected algebraic group with Lie algebra $\mathfrak N$, defined intrinsically by its algebraic hull. Then
--
--   $$I\cap F[x_{ij}]=\{f\in F[x_{ij}]:f(a)=0\text{ for every }a\in G(\mathfrak N)\}.$$
--
--   Thus the graph construction recovers the full vanishing ideal, beyond merely a set of defining equations.
-- source:
--   Constructing algebraic groups from their Lie algebras, arXiv:math/0612557v1, PDF p. 4, Proposition 4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P22

open scoped BigOperators Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing

section Geometric

variable {F K : Type*} [Field F] [hchar : CharZero F] [Field K] [Algebra F K] [hclosure : IsAlgClosure F K]

variable {n : ℕ}

section

include hchar hclosure

/-- Proposition 4, PDF p.4: the graph contraction is the entire F-vanishing ideal of G(N).
The source proof's missing exponential is read using its displayed construction. -/
theorem nilpotent_elimination_vanishing {r : ℕ}
    (N : LieSubalgebra F (Matrix (Fin n) (Fin n) F)) (B : Module.Basis (Fin r) F N)
    (hN : ∀ X : N, IsNilpotent (X : Matrix (Fin n) (Fin n) F)) :
    nilpotentEliminationIdeal (fun i => (B i : Matrix (Fin n) (Fin n) F)) =
      vanishingIdeal F (groupHull F K N.toSubmodule : Set (GeometricGL n K)) := by sorry

end

end Geometric

end QAlgorithms.Papers.Independent.Renew46.P22

end

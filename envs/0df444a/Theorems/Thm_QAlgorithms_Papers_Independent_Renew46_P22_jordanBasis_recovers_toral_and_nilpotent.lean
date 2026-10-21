-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P22_jordanBasis_recovers_toral_and_nilpotent
-- name    : QAlgorithms.Papers.Independent.Renew46.P22.jordanBasis_recovers_toral_and_nilpotent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:36:35.733266+00:00
-- url     : https://prove2.me/theorems/192bc7af-ef18-492f-9459-1aa2d562f9bb
-- title:
--   Jordan parts of a Cartan basis recover the toral and nilpotent summands
-- statement:
--   Let $F$ be a field of characteristic zero and let $K$ be its specified algebraic closure, with its embedding of $F$. All groups below are geometric subgroups of $\mathrm{GL}_n(K)$, and all closures are relative Zariski closures in that group.
--
--   Let $\mathfrak g\subseteq\mathfrak{gl}_n(F)$ be the Lie algebra of a connected algebraic group defined over $F$. Write $\mathfrak s=\operatorname{rad}(\mathfrak g)$ and let $\mathfrak n$ be its largest ideal consisting of nilpotent ambient matrices. Assume the section’s starting structure: an abelian matrix-semisimple subalgebra $\mathfrak d\subseteq\mathfrak s$ satisfies $\mathfrak s=\mathfrak d\ltimes\mathfrak n$, and $\mathfrak n$ is exactly the set of nilpotent matrices in $\mathfrak s$. Let $\mathfrak h^\ast,\mathfrak d^\ast$ satisfy every conclusion of Lemma 10: $\mathfrak h^\ast$ is Cartan, $\mathfrak d^\ast$ is an abelian matrix-semisimple complement to $\mathfrak n$, and $\mathfrak h^\ast=C_{\mathfrak s}(\mathfrak d^\ast)=\mathfrak d^\ast+C_{\mathfrak n}(\mathfrak d^\ast)$. Take a complete $F$-basis $a_1,\ldots,a_r$ of $\mathfrak h^\ast$ and its ambient matrix Jordan decompositions $a_i=s_i+n_i$. Define $\mathfrak s_1(\mathfrak h^\ast)=\bigcap_{k>0}[ (\mathfrak h^\ast)^k,\mathfrak s]$, where the bracket space has $k$ repeated factors of $\mathfrak h^\ast$. Then
--
--   $$\mathfrak d^\ast=\operatorname{span}_F\{s_1,\ldots,s_r\},\qquad \mathfrak n=\operatorname{span}_F\{n_1,\ldots,n_r\}+\mathfrak s_1(\mathfrak h^\ast).$$
--
--   The Fitting component is an intersection of iterated bracket spaces. This recovers the two summands from a full Cartan basis.
-- source:
--   Constructing algebraic groups from their Lie algebras, arXiv:math/0612557v1, PDF p. 9, Lemma 11

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

/-- Lemma 11, PDF p.9: Jordan parts of a complete Cartan basis recover dnew and n. -/
theorem jordanBasis_recovers_toral_and_nilpotent {r : ℕ}
    (g : LieSubalgebra F (Matrix (Fin n) (Fin n) F)) (d : LieSubalgebra F g)
    (ctx : SolvableContext (K := K) g d)
    (h dnew : LieSubalgebra F g) (hh : IsCartanInRadical g h)
    (hdnew : ToralComplement g dnew)
    (hc : h = centralizerWithin (LieAlgebra.radical F g).toLieSubalgebra dnew)
    (hsum : h.toSubmodule = dnew.toSubmodule ⊔
      (centralizerWithin (matrixNilpotentIdeal g).toLieSubalgebra dnew).toSubmodule)
    (B : Module.Basis (Fin r) F h) :
    ambientSubmodule g dnew.toSubmodule =
      Submodule.span F (Set.range (fun i => semisimplePart ((B i : g) : Matrix (Fin n) (Fin n) F))) ∧
    ambientSubmodule g (matrixNilpotentIdeal g).toSubmodule =
      Submodule.span F (Set.range (fun i => nilpotentPart ((B i : g) : Matrix (Fin n) (Fin n) F))) ⊔
      ambientSubmodule g (fittingOne h.toSubmodule (LieAlgebra.radical F g).toSubmodule) := by sorry

end

end LieStructure

end QAlgorithms.Papers.Independent.Renew46.P22

end

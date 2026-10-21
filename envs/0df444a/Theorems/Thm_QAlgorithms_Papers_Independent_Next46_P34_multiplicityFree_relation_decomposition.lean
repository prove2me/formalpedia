-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P34_multiplicityFree_relation_decomposition
-- name    : QAlgorithms.Papers.Independent.Next46.P34.multiplicityFree_relation_decomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:32:22.133804+00:00
-- url     : https://prove2.me/theorems/bd87b02c-d5ce-47cd-bdd2-631b321b81a7
-- title:
--   Multiplicity-free decomposition of rational and integral root relations
-- statement:
--   Let $f\in\mathbb Z[T]$ be monic and square-free, of positive degree $n$, and let $K/\mathbb Q$ be its splitting field. List all its roots as $\alpha_1,\ldots,\alpha_n$. The Galois group $G=\operatorname{Aut}_{\mathbb Q}(K)$ acts on $M=\mathbb Q^n$ by inverse permutation of coordinates. Suppose
--   $$M=\bigoplus_{i=1}^r V_i$$
--   is an internal decomposition into nonzero irreducible rational $G$-submodules, no two of which are isomorphic. Choose a rational basis $B_i$ of each $V_i$. Define $\ell(e)=\sum_k e_k\alpha_k$, $\Lambda_{\mathbb Q}=\ker\ell$, and $\Lambda=\{e\in\mathbb Z^n:\sum_k e_k\alpha_k=0\}$. Set $J=\{i:\ell(b)=0\text{ for every }b\in B_i\}$. Then
--   $$\Lambda_{\mathbb Q}=\bigoplus_{i\in J}V_i,\qquad \Lambda=\mathbb Z^n\cap\bigoplus_{i\in J}V_i.$$
--   The intersection uses the coordinate inclusion $\mathbb Z^n\hookrightarrow\mathbb Q^n$. This is a mathematical component characterization; the printed approximate verifier is separately deferred.
-- source:
--   Constructing algebraic Lie algebras, arXiv:math/0611414v1, PDF p. 14, §6 Remark: multiplicity-free relation-space decomposition

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P34

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P34

/-- Fieker–de Graaf, arXiv:math/0611414v1, PDF p.14, Remark.
For a multiplicity-free decomposition, the rational relation space is exactly
the sum of the components whose basis vectors are relations, in Section 6's
monic integral square-free polynomial setting over Q.
Printed: the final sentence calls the rational summand sum Lambda.
Changed: use Lambda_Q for that sum and take its integer-coordinate intersection
for Lambda. Why: the preceding displayed identity and Section 4 distinguish the
rational subspace from the integral lattice. -/
theorem multiplicityFree_relation_decomposition
    {K : Type*} [Field K] [CharZero K]
    [Algebra ℚ K] [FiniteDimensional ℚ K]
    {n : ℕ} (hn : 0 < n) (f : Polynomial ℤ)
    (hmonic : f.Monic) (hsquarefree : Squarefree f)
    [Polynomial.IsSplittingField ℚ K (f.map (algebraMap ℤ ℚ))]
    (alpha : Fin n → K)
    (hroots : f.map (algebraMap ℤ K) =
      ∏ k, (Polynomial.X - Polynomial.C (alpha k)))
    (action : (K ≃ₐ[ℚ] K) →* Equiv.Perm (Fin n))
    (hrootAction : ∀ (sigma : K ≃ₐ[ℚ] K) k, sigma (alpha k) = alpha (action sigma k))
    {r : ℕ} (V : Fin r → Submodule ℚ (Fin n → ℚ))
    (hdecomposition : DirectSum.IsInternal V)
    (hirreducible : ∀ i, IsIrreducibleComponent action (V i))
    (hnonisomorphic : Pairwise (fun i j => ¬ EquivariantlyIsomorphic action (V i) (V j)))
    (d : Fin r → ℕ) (b : ∀ i, Module.Basis (Fin (d i)) ℚ (V i)) :
    rationalRelations alpha = selectedComponentSum alpha V b ∧
      (integerRelations alpha : Set (Fin n → ℤ)) =
        {e | (fun k => (e k : ℚ)) ∈ selectedComponentSum alpha V b} := by sorry

end QAlgorithms.Papers.Independent.Next46.P34

end

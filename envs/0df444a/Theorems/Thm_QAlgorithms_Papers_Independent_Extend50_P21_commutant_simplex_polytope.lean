-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_commutant_simplex_polytope
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.commutant_simplex_polytope
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:13:18.75429+00:00
-- url     : https://prove2.me/theorems/7ac62f15-d170-4349-b35b-92dc8550a14e
-- title:
--   Lemma 16: abelian commutant, simplex, and polytope equivalence
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. Let $G$ be a compact Lie group, $U$ a continuous unitary representation on the input $\mathcal H_1$, and $V$ one on the output $\mathcal H_2$, of dimensions $d_1,d_2>0$. Write $\mathcal T_{UV}$ for the CPTP maps satisfying $T(U_gAU_g^*)=V_gT(A)V_g^*$ for every operator $A$ and $g\in G$. The normalized, reference-first Choi operator is $c_T=(\mathrm{id}_{d_1}\otimes T)(|\Omega\rangle\langle\Omega|)$, where $|\Omega\rangle=d_1^{-1/2}\sum_i|i,i\rangle$, with two input-sized factors before $T$ acts. In an actual unitary isotypic decomposition $\overline U\otimes V\simeq\bigoplus_{k=1}^K W_k\otimes I_{n_k}$, the $W_k$ are pairwise inequivalent occurring irreducibles with positive dimensions $b_k$, and $n_k>0$ are their multiplicities. Put $d_c=\sum_k n_k$ and $d_n=\sum_k n_k^2$. Assume $U$ is irreducible and set $J_{UV}=\{c_T:T\in\mathcal T_{UV}\}$. Then
--
--   $$\mathcal K\text{ is abelian}\ \Longleftrightarrow\ J_{UV}\text{ is a finite simplex}\ \Longleftrightarrow\ J_{UV}\text{ is a finite polytope}.$$
--
--   Here isomorphism is affine, preserving convex combinations. In the abelian case $J_{UV}$ is the convex hull of $K$ affinely independent vertices, so it has affine dimension $K-1$, including a single point when $K=1$. This distinguishes the channel classes admitting a finite extreme-point description.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 8, Lemma 16: abelian commutant, simplex, and polytope equivalence

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible EquivalentModels)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

namespace QAlgorithms.Papers.Independent.Extend50.P21

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

section General

variable {G I O : Type*} [Group G] [TopologicalSpace G]

variable [Fintype I] [DecidableEq I] [inputNonempty : Nonempty I]

variable [Fintype O] [DecidableEq O] [outputNonempty : Nonempty O]

include inputNonempty outputNonempty

/-- PDF pp.8--9, Lemma 16: the three-way affine convex-geometric equivalence.
In the commutative case there are exactly K affinely independent vertices. -/
theorem commutant_simplex_polytope (hG : CompactLie G)
    (U : ContinuousUnitaryRep G I) (V : ContinuousUnitaryRep G O) (hU : Irreducible U.mat) (D : TensorIsotypicDecomposition U V) :
    ((CommutativeMatrixSet (covariantTensorCommutant U.mat V.mat) ↔ Simplex (choiSet (covariantChannels U.mat V.mat))) ∧
      (Simplex (choiSet (covariantChannels U.mat V.mat)) ↔
        Polytope (choiSet (covariantChannels U.mat V.mat)))) ∧
    (CommutativeMatrixSet (covariantTensorCommutant U.mat V.mat) →
      ∃ vertices : Fin D.count → Matrix (I × O) (I × O) ℂ,
        AffineIndependent ℝ vertices ∧
        convexHull ℝ (Set.range vertices) = choiSet (covariantChannels U.mat V.mat)) := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P21

end

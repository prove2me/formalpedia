-- Prove2me | Theorems.Thm_TensorProduct_mulMap_injOn_and_surjOn_diagonal_of_isSeparable
-- name    : TensorProduct.mulMap_injOn_and_surjOn_diagonal_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/7e4a1a60-4413-5148-8c11-b343a3d5ec26
-- title:
--   Multiplication is bijective on the diagonal of K ⊗_F P
-- statement:
--   Let $F \subseteq K$ be a finite separable extension of fields, and let $P$ be an abelian group carrying compatible $F$- and $K$-module structures (a $K$-vector space, with its $F$-structure obtained by restriction). On $K \otimes_F P$ there are two actions of $K$: the $K$-module structure coming from the left tensor factor, written $k \cdot w$, and, for each $k \in K$, the base change to $K$ of the $F$-linear endomorphism $v \mapsto k \cdot v$ of $P$, i.e. the map sending $a \otimes v$ to $a \otimes k v$. Call $w \in K \otimes_F P$ diagonal if these two agree on $w$ for every $k \in K$. Let $\pi \colon K \otimes_F P \to P$ be a $K$-linear map with $\pi(a \otimes v) = a \cdot v$ for all $a \in K$, $v \in P$ (the multiplication map). The assertion is the conjunction of two statements: first, a diagonal $w$ with $\pi(w) = 0$ is $0$; second, every $v \in P$ is of the form $\pi(w)$ for some diagonal $w$. Thus $\pi$ restricts to a bijection from the diagonal subspace onto $P$.
--
--   This is the standard consequence of separability of $K/F$ that the two commuting $K$-actions on $K \otimes_F P$ have a 'diagonal' locus mapped isomorphically onto $P$ by multiplication, the mechanism behind the existence of a separability idempotent in $K \otimes_F K$. It is used in the analysis of the rational Tate module, in [`ModularCurve.rationalTateModule_false_of_inertia_fixed_eigenplane`](thm.html#ModularCurve.rationalTateModule_false_of_inertia_fixed_eigenplane), to descend a $K$-stable eigenplane condition along a tensor product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TensorProduct_mulMap_injOn_and_surjOn_diagonal_of_isSeparable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem TensorProduct.mulMap_injOn_and_surjOn_diagonal_of_isSeparable
    {F K P : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Algebra.IsSeparable F K]
    [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P]
    (π : K ⊗[F] P →ₗ[K] P) (hπ : ∀ (a : K) (v : P), π (a ⊗ₜ[F] v) = a • v) :
    (∀ w : K ⊗[F] P,
        (∀ k : K, k • w = LinearMap.baseChange K ((LinearMap.lsmul K P k).restrictScalars F) w) →
          π w = 0 → w = 0) ∧
      ∀ v : P, ∃ w : K ⊗[F] P,
        (∀ k : K, k • w = LinearMap.baseChange K ((LinearMap.lsmul K P k).restrictScalars F) w) ∧ π w = v := by sorry

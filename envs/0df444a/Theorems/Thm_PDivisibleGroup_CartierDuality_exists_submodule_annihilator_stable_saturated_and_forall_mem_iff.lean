-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_exists_submodule_annihilator_stable_saturated_and_forall_mem_iff
-- name    : PDivisibleGroup.CartierDuality.exists_submodule_annihilator_stable_saturated_and_forall_mem_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/49598805-0b8a-5843-b0bd-8de0a0533933
-- title:
--   Annihilator of a saturated Galois-stable submodule under a Tate pairing
-- statement:
--   Let $R$ be a commutative ring, let $p$ be prime and $h$ a natural number, and let $A,A'$ be $p$-divisible groups over $R$ of height parameter $h$ equipped with a Cartier duality $D$ (levelwise coalgebra isomorphisms $A'.\mathrm{level}\,v \simeq \mathrm{CartierDual}\,R\,(A.\mathrm{level}\,v)$ compatible with the transition maps). Let $L$ be an algebraically closed field of characteristic zero that is an $R$-algebra, and write $T(\,\cdot\,)$ for the Tate module of an abelian group $M$, namely the group of sequences $(x_n)_{n\in\mathbb N}$ in $M$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, a $\mathbb Z_p$-module. Let $B$ be a $\mathbb Z_p$-bilinear map $T(A(L)) \times T(A'(L)) \to T(\mathrm{Additive}\,L^\times)$ subject to two hypotheses: first, whenever $f$ is an $L$-point of $A$ at level $v$ and $g$ one of $A'$ at level $v$ whose images under the direct-limit maps into $A.\mathrm{Points}\,L$, $A'.\mathrm{Points}\,L$ are the $v$-th components of $x$ and $y$ respectively, the $v$-th component of $B\,x\,y$, read in $L^\times \subseteq L$, equals the Cartier pairing value $D.\mathrm{pair}\,L\,v\,f\,g$; second, for every $R$-algebra automorphism $\sigma$ of $L$ and every $x,y,v$, the $v$-th component of $B$ applied to the componentwise $\sigma$-translates of $x$ and $y$ is $\sigma$ of the $v$-th component of $B\,x\,y$. Let $M \subseteq T(A'(L))$ be a $\mathbb Z_p$-submodule stable under the componentwise action of every $\sigma \in \mathrm{Aut}_R(L)$ and saturated, in the sense that $r \neq 0$ and $r\cdot x \in M$ imply $x \in M$. Then there is a $\mathbb Z_p$-submodule $N \subseteq T(A(L))$ whose members are exactly the $y$ with $B\,y\,x = 0$ for all $x \in M$, which is stable under the componentwise action of every $\sigma \in \mathrm{Aut}_R(L)$ and saturated, and which satisfies the double-annihilator identity: $x \in M$ if and only if $B\,y\,x = 0$ for all $y \in N$.
--
--   This is the linear-algebra bookkeeping attached to Tate's pairing of the Tate modules of two $p$-divisible groups in Cartier duality: the orthogonal complement of a saturated Galois-stable submodule is again a saturated Galois-stable submodule, and taking complements twice returns the original submodule. It is used to pass between the "sub" and "quotient/image" formulations of statements about $p$-divisible subgroups, and is cited in the construction of a $p$-divisible group with prescribed Tate module kernel over a ring of integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_exists_submodule_annihilator_stable_saturated_and_forall_mem_iff.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_CartierDuality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.exists_submodule_annihilator_stable_saturated_and_forall_mem_iff
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {A A' : PDivisibleGroup R p h}
    (D : A.CartierDuality A') (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    (B : TateModule p (A.Points L) →ₗ[ℤ_[p]] TateModule p (A'.Points L) →ₗ[ℤ_[p]] TateModule p (Additive Lˣ))
    (hB : (∀ (x : TateModule p (A.Points L)) (y : TateModule p (A'.Points L)) (v : ℕ)
        (f : A.Point L v) (g : A'.Point L v),
        A.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → A.Points L) v →
        A'.pointsMkAdd L v (Additive.ofMul g) = (y : ℕ → A'.Points L) v →
        ((Additive.toMul ((B x y : ℕ → Additive Lˣ) v) : Lˣ) : L) = D.pair L v f g))
    (hBσ : ∀ (σ : L ≃ₐ[R] L) (x : TateModule p (A.Points L)) (y : TateModule p (A'.Points L)) (v : ℕ),
        ((Additive.toMul ((B (A.tateModuleRep L σ x) (A'.tateModuleRep L σ y) : ℕ → Additive Lˣ) v) : Lˣ) : L) =
          σ (((Additive.toMul ((B x y : ℕ → Additive Lˣ) v) : Lˣ) : L)))
    (M : Submodule ℤ_[p] (TateModule p (A'.Points L)))
    (hMstab : ∀ (σ : L ≃ₐ[R] L) (x : TateModule p (A'.Points L)), x ∈ M → A'.tateModuleRep L σ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (A'.Points L)), r ≠ 0 → r • x ∈ M → x ∈ M) :
    ∃ N : Submodule ℤ_[p] (TateModule p (A.Points L)),
      (∀ y : TateModule p (A.Points L), y ∈ N ↔ ∀ x ∈ M, B y x = 0) ∧
      (∀ (σ : L ≃ₐ[R] L) (y : TateModule p (A.Points L)), y ∈ N → A.tateModuleRep L σ y ∈ N) ∧
      (∀ (r : ℤ_[p]) (y : TateModule p (A.Points L)), r ≠ 0 → r • y ∈ N → y ∈ N) ∧
      (∀ x : TateModule p (A'.Points L), x ∈ M ↔ ∀ y ∈ N, B y x = 0) := by sorry

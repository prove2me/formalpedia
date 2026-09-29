-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_tateModuleRep_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_of_forall_pair_eq_one
-- name    : PDivisibleGroup.CartierDuality.tateModuleRep_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_of_forall_pair_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/f8d8f42d-00ad-5cb0-8458-041e3ae1e425
-- title:
--   Inertia acts on formal Tate vectors by the cyclotomic character
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with an algebra map to $\overline{\mathbb{Q}}$, and a valuation subring $P$ of $\overline{\mathbb{Q}}$ such that every element of the image of $O$ lies in $P$. Let $H,H'$ be $p$-divisible groups over $O$ of height $h$ (finite free Hopf algebras `level v` of rank $p^{vh}$ with surjective transitions whose kernels are the $p^v$-torsion ideals) and let $D$ be a Cartier duality datum between them, i.e. coalgebra-algebra isomorphisms $H'.\mathrm{level}\,v \simeq \mathrm{CartierDual}_O(H.\mathrm{level}\,v)$ compatible with transition and multiplication by $p$. Assume (orthogonality) that for every level $v$ and all points $f : H.\mathrm{level}\,v \to \overline{\mathbb{Q}}$, $\psi : H'.\mathrm{level}\,v \to \overline{\mathbb{Q}}$ with $P$-valuation of $f(a)-\varepsilon(a)$ and of $\psi(a)-\varepsilon(a)$ strictly less than $1$ for all $a$ ($\varepsilon$ the counit), the Cartier pairing $D.\mathrm{pair}$ of $f$ and $\psi$ equals $1$. Let $\tau$ be a $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ lying in the image of the inertia subgroup of $P$ over $\mathbb{Q}$, let $\tau'$ be an $O$-automorphism of $\overline{\mathbb{Q}}$ with the same underlying map, and let $x$ be a Tate vector for $H$, that is a sequence $(x_n)$ in $H.\mathrm{Points}(\overline{\mathbb{Q}})$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, such that each $x_n$ comes from a point $f$ at some level $w$ with $P$-valuation of $f(a)-\varepsilon(a)$ less than $1$ for all $a$. Then the componentwise action of $\tau'$ on $x$ equals $\chi_p(\tau)\cdot x$, where $\chi_p$ is the $p$-adic cyclotomic character of $\overline{\mathbb{Q}}$ viewed in $\mathbb{Z}_p$.
--
--   This is the standard statement that inertia acts on the formal (connected) part of the Tate module of a $p$-divisible group through the cyclotomic character, obtained here from Galois equivariance of the Cartier pairing on Tate modules together with the assumed orthogonality of formal points. It feeds into the analysis of the Galois action attached to a $p$-divisible group whose reduction satisfies a Frobenius-Verschiebung relation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_tateModuleRep_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_of_forall_pair_eq_one.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_PDivisibleGroup_CartierDuality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.CartierDuality.tateModuleRep_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_of_forall_pair_eq_one
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    {h : ℕ} {H H' : PDivisibleGroup O p h} (D : H.CartierDuality H')

    (horth : ∀ (v : ℕ) (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v),
      (∀ a : H.level v, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : H'.level v, P.valuation (PDivisibleGroup.Point.toAlgHom ψ a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      D.pair (AlgebraicClosure ℚ) v f ψ = 1)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ)
    (hττ' : ∀ x : AlgebraicClosure ℚ, τ' x = τ x) (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (x : TateModule p (H.Points (AlgebraicClosure ℚ)))

    (hx : ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
      ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) :
    H.tateModuleRep (AlgebraicClosure ℚ) τ' x =
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x := by sorry

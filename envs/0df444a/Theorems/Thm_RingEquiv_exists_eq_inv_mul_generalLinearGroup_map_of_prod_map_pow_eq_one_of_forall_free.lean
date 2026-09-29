-- Prove2me | Theorems.Thm_RingEquiv_exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free
-- name    : RingEquiv.exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/79d433dc-42cd-5464-adbf-a2f11d12b7bd
-- title:
--   Hilbert's Theorem 90 for GL_m over a cyclic algebra
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$ of finite order, written $n = \operatorname{orderOf} \sigma$, with $0 < n$. Let $S$ be a commutative ring that is an $L$-algebra and let $\theta$ be a ring automorphism of $S$ which is $\sigma$-semilinear in the sense that $\theta(\mathrm{alg}_{L\to S}(l)) = \mathrm{alg}_{L\to S}(\sigma l)$ for all $l \in L$, and which satisfies $\theta^{n} = 1$. Write $R$ for the subring $\{s \in S : \theta(s) = s\}$, realised as the equaliser locus of $\theta$ and the identity ring homomorphism of $S$. Let $m$ be a natural number and assume the freeness hypothesis: every $R$-module $P$ admitting an $R$-linear isomorphism $P^{n} \cong R^{mn}$ (indexed by $\mathrm{Fin}\,n$ and $\mathrm{Fin}\,(mn)$ respectively) is a free $R$-module. Then for every $x \in \mathrm{GL}_m(S)$ whose ordered cyclic norm vanishes to $1$, i.e. the product over $k = 0, \dots, n-1$ in that order of the images of $x$ under the maps $\mathrm{GL}_m(S) \to \mathrm{GL}_m(S)$ induced by $\theta^{k}$ equals $1$, there exists $y \in \mathrm{GL}_m(S)$ with $x = y^{-1}\,\theta(y)$, where $\theta$ acts on $\mathrm{GL}_m(S)$ entrywise.
--
--   This is Speiser's form of Hilbert's Theorem 90 for $\mathrm{GL}_m$, transposed from a cyclic field extension to a cyclic Galois algebra: a matrix of cyclic norm one is a twisted coboundary, subject to the hypothesis that the relevant modules over the invariant ring are free. It is used in the automorphic part of the argument, where $\sigma$-conjugation of matrices over adelic rings has to be trivialised.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingEquiv_exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RingEquiv.exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free
    (K L : Type) [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (hσ : 0 < orderOf σ)
    (S : Type) [CommRing S] [Algebra L S] (θ : S ≃+* S)
    (hθ : ∀ l : L, θ (algebraMap L S l) = algebraMap L S (σ l))
    (hθn : θ ^ orderOf σ = 1)
    (m : ℕ)
    (hfree : ∀ (P : Type) [AddCommGroup P] [Module (RingHom.eqLocus θ.toRingHom (RingHom.id S)) P],
      ((Fin (orderOf σ) → P) ≃ₗ[RingHom.eqLocus θ.toRingHom (RingHom.id S)]
          (Fin (m * orderOf σ) → RingHom.eqLocus θ.toRingHom (RingHom.id S))) →
        Module.Free (RingHom.eqLocus θ.toRingHom (RingHom.id S)) P)
    (x : GL (Fin m) S)
    (hx : ((List.range (orderOf σ)).map
      fun k => Matrix.GeneralLinearGroup.map ((θ ^ k : S ≃+* S) : S →+* S) x).prod = 1) :
    ∃ y : GL (Fin m) S, x = y⁻¹ * Matrix.GeneralLinearGroup.map (θ : S →+* S) y := by sorry

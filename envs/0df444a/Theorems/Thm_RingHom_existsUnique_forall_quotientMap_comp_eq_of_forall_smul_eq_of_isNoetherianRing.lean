-- Prove2me | Theorems.Thm_RingHom_existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing
-- name    : RingHom.existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/2fdc8c56-6ec5-5358-9935-0f1d2600d647
-- title:
--   Invariant compatible families of formal points descend to R
-- statement:
--   Let $R$ be a Noetherian commutative ring, $A$ a commutative $R$-algebra which is finite as an $R$-module, and $C$ an arbitrary commutative ring; let $G$ be a finite group acting on $A$ by ring automorphisms in such a way that the action commutes with the $R$-action on $A$. Assume that $\mathrm{algebraMap}\colon R \to A$ is injective and that every $a \in A$ fixed by all $g \in G$ lies in the image of $\mathrm{algebraMap}$. Fix $\pi \in R$, and suppose given, for every $n \in \mathbb{N}$, a ring homomorphism $c_n \colon C \to A/(\mathrm{algebraMap}(\pi)^n)$ such that the reduction map $A/(\mathrm{algebraMap}(\pi)^{n+1}) \to A/(\mathrm{algebraMap}(\pi)^n)$ composed after $c_{n+1}$ equals $c_n$, and such that the family is $G$-invariant in the following sense: for all $n$, all $g \in G$, all $z \in C$ and all $a \in A$ whose class modulo $\mathrm{algebraMap}(\pi)^n$ equals $c_n(z)$, the class of $g \cdot a$ modulo $\mathrm{algebraMap}(\pi)^n$ again equals $c_n(z)$. The assertion is that there is a unique family of ring homomorphisms $d_n \colon C \to R/(\pi^n)$, $n \in \mathbb{N}$, compatible with the reduction maps $R/(\pi^{n+1}) \to R/(\pi^n)$, such that for every $n$ the composite of $d_n$ with the map $R/(\pi^n) \to A/(\mathrm{algebraMap}(\pi)^n)$ induced by $\mathrm{algebraMap}$ is $c_n$.
--
--   This is the ring-theoretic form of the statement that a $G$-invariant point of the $\pi$-adic formal completion of $\operatorname{Spec} A$, for a finite group $G$ acting on a finite $R$-algebra $A$ with invariants $R$, comes from a unique point of the $\pi$-adic formal completion of $\operatorname{Spec} R$; invariance of a single $c_n$ would not suffice, it is the whole compatible system, i.e. a map into the completion, that descends. It is used to prove the corresponding statement for affine Noetherian schemes, [`AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing`](thm.html#AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RingHom.existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing
    (R A C : Type) [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing C]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A]
    (hinj : Function.Injective (algebraMap R A))
    (hinv : ∀ a : A, (∀ g : G, g • a = a) → a ∈ Set.range (algebraMap R A))
    (π : R)
    (c : ∀ n : ℕ, C →+* A ⧸ Ideal.span {algebraMap R A π ^ n})
    (hc : ∀ n : ℕ, (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap R A π) (Nat.le_succ n)))).comp (c (n + 1)) = c n)
    (hG : ∀ (n : ℕ) (g : G) (z : C) (a : A), Ideal.Quotient.mk _ a = c n z →
        Ideal.Quotient.mk (Ideal.span {algebraMap R A π ^ n}) (g • a) = c n z) :
    ∃! d : ∀ n : ℕ, C →+* R ⧸ Ideal.span {π ^ n},
      (∀ n : ℕ, (Ideal.Quotient.factor
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ n)))).comp (d (n + 1)) = d n) ∧
      (∀ n : ℕ, (Ideal.quotientMap (Ideal.span {algebraMap R A π ^ n}) (algebraMap R A)
          (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← map_pow]; exact Ideal.subset_span rfl)).comp (d n) = c n) := by sorry

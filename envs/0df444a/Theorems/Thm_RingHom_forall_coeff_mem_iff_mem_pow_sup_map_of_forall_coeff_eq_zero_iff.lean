-- Prove2me | Theorems.Thm_RingHom_forall_coeff_mem_iff_mem_pow_sup_map_of_forall_coeff_eq_zero_iff
-- name    : RingHom.forall_coeff_mem_iff_mem_pow_sup_map_of_forall_coeff_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/ed7dc3fb-3e55-538b-9ec7-264eee0daab1
-- title:
--   Low coefficients in 𝔪 iff membership in Iⁿ + 𝔪 A
-- statement:
--   Let $R$ and $A$ be commutative rings with $A$ an $R$-algebra, let $\theta : A \to R[[X]]$ be a ring homomorphism, and let $I$ be an ideal of $A$. Assume three conditions on $\theta$: it is $R$-linear on constants, in the sense that $\theta(\mathrm{algebraMap}_{R,A}(r)) = C(r)$ for every $r \in R$; it detects the $I$-adic filtration, in that for all $n \in \mathbb{N}$ and $a \in A$ one has $\mathrm{coeff}_k(\theta a) = 0$ for all $k < n$ if and only if $a \in I^n$; and it is surjective modulo $X^n$, in that for every $n \in \mathbb{N}$ and every power series $p \in R[[X]]$ there is $a \in A$ with $\mathrm{coeff}_k(\theta a) = \mathrm{coeff}_k(p)$ for all $k < n$. Then for every ideal $\mathfrak m$ of $R$, every $n \in \mathbb{N}$ and every $a \in A$, the coefficients $\mathrm{coeff}_k(\theta a)$ lie in $\mathfrak m$ for all $k < n$ if and only if $a$ belongs to the ideal $I^n \sqcup \mathfrak m \cdot A$, the supremum of $I^n$ and the image ideal $\mathfrak m.\mathrm{map}(\mathrm{algebraMap}_{R,A})$.
--
--   This says that a power-series expansion along a section, with the stated exactness properties for the $I$-adic filtration, remains exact after reducing the coefficients modulo an ideal $\mathfrak m$ of the base: the first coefficient not lying in $\mathfrak m$ computes the $I$-adic order of the reduction of $a$. It is used in the analysis of the model of the modular curve at $p$, in the two results [`ModularCurve.XHDRModelAtP.residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictFst`](thm.html#ModularCurve.XHDRModelAtP.residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictFst) and `...IsStrictSnd`, to identify the order of a residue from the coefficients of its expansion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_forall_coeff_mem_iff_mem_pow_sup_map_of_forall_coeff_eq_zero_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open PowerSeries

theorem RingHom.forall_coeff_mem_iff_mem_pow_sup_map_of_forall_coeff_eq_zero_iff
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (θ : A →+* PowerSeries R) (I : Ideal A)
    (hC : ∀ r : R, θ (algebraMap R A r) = PowerSeries.C r)
    (hfil : ∀ (n : ℕ) (a : A), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔ a ∈ I ^ n)
    (hsurj : ∀ (n : ℕ) (p : PowerSeries R), ∃ a : A, ∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = PowerSeries.coeff k p)
    (𝔪 : Ideal R) (n : ℕ) (a : A) :
    (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) ∈ 𝔪) ↔ a ∈ I ^ n ⊔ 𝔪.map (algebraMap R A) := by sorry

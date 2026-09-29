-- Prove2me | Theorems.Thm_PadicAlgCl_exists_unramified_level_char_of_sq_sub_one_mem_span_socle
-- name    : PadicAlgCl.exists_unramified_level_char_of_sq_sub_one_mem_span_socle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/64724c6e-472d-5302-ae66-fa91da44981e
-- title:
--   Unramified order-p character from a socle deviation of z²
-- statement:
--   Let $p$ be a prime and $B$ a finite commutative local ring in which the image of $p$ lies in the maximal ideal. Let $z$ be a function from $G_p := \mathrm{Gal}(\mathrm{PadicAlgCl}\,p/\mathbb{Q}_p)$ to $B^\times$ which is multiplicative, $z(gh)=z(g)z(h)$; let $F$ be a finite-dimensional intermediate field of $\mathbb{Q}$ in $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ and assume $z(s)=1$ whenever the global automorphism $\mathrm{localGaloisToGlobal}\ p\ s$ (restrict $s$ to $\mathbb{Q}$-scalars, then take its restriction to the normal closure $\mathrm{AlgebraicClosure}\,\mathbb{Q}$) fixes $F$ pointwise; assume also $z(\tau)=1$ for every $\tau$ in the inertia subgroup, i.e. the image in $G_p$ of the inertia subgroup of the decomposition subgroup over $\mathbb{Q}_p$ of the valuation subring of $\mathrm{PadicAlgCl}\,p$. Let $t$ be an element of the maximal ideal annihilating the maximal ideal, and suppose $z(g)^2-1\in(t)$ for all $g$, while $z(g)^2\neq 1$ for at least one $g$. Then there are a unit $\eta\in B$ and a function $\chi:G_p\to\mathbb{Z}$ such that $\chi$ is level-constant for $\mathrm{localGaloisToGlobal}\ p$ in the sense of [`groupCohomology.IsLevelConstant₁`](def/GroupCohomology_ContinuousH2.html#L14); $\chi(g)+\chi(h)-\chi(gh)\equiv 0 \pmod p$ for all $g,h$; for each $g$, $g$ fixes every $(p^p-1)$-st root of unity in $\mathrm{PadicAlgCl}\,p$ if and only if $p\mid\chi(g)$; and $z(g)^2=1+t\eta\,\chi(g)$ for all $g$.
--
--   This is the local analysis at $p$ of a multiplicative function whose square deviates from $1$ only in the socle direction $t$: the deviation is governed by an unramified additive character of order $p$, whose kernel is exactly the subgroup fixing $\mu_{p^p-1}$, that is, the Galois group of the unramified extension of $\mathbb{Q}_p$ of degree $p$. It is used by [`PadicAlgCl.exists_isUnit_forall_dvd_valuation_of_thickening`](thm.html#PadicAlgCl.exists_isUnit_forall_dvd_valuation_of_thickening).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_exists_unramified_level_char_of_sq_sub_one_mem_span_socle.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.exists_unramified_level_char_of_sq_sub_one_mem_span_socle
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime]
    (hpB : (p : B) ∈ IsLocalRing.maximalIdeal B)
    (z : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → Bˣ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : FiniteDimensional ℚ F)
    (hzmul : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), z (g * h) = z g * z h)
    (hzlev : ∀ s : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), localGaloisToGlobal p s ∈ F.fixingSubgroup → z s = 1)
    (hzI : ∀ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → z τ = 1)
    (t : B) (htm : t ∈ IsLocalRing.maximalIdeal B)
    (htk : ∀ m ∈ IsLocalRing.maximalIdeal B, t * m = 0)
    (hsq : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) - 1 ∈ Ideal.span {t})
    (hne : ∃ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) ≠ 1) :
    ∃ (η : B) (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℤ), IsUnit η ∧
      groupCohomology.IsLevelConstant₁ (localGaloisToGlobal p) χ ∧
      (∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (p : ℤ) ∣ χ g + χ h - χ (g * h)) ∧
      (∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (∀ w : PadicAlgCl p, w ^ (p ^ p - 1) = 1 → g w = w) ↔ (p : ℤ) ∣ χ g) ∧
      (∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) = 1 + t * η * (χ g : B)) := by sorry

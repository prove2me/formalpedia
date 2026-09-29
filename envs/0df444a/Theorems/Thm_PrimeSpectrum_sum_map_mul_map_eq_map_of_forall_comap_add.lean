-- Prove2me | Theorems.Thm_PrimeSpectrum_sum_map_mul_map_eq_map_of_forall_comap_add
-- name    : PrimeSpectrum.sum_map_mul_map_eq_map_of_forall_comap_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/a9305271-326d-57d5-9de3-8b2f9da4a9b9
-- title:
--   Convolution identity for idempotents cutting out an additive cocycle
-- statement:
--   Let $R$ and $S$ be commutative rings and let $\iota$ be a finite additively written abelian group. Let $\varphi_{12},\varphi_{23},\varphi_{13}\colon R\to S$ be ring homomorphisms, let $f\colon\operatorname{Spec}R\to\iota$ be a function on the prime spectrum, and let $e\colon\iota\to R$ be a family of elements of $R$ which is a complete system of orthogonal idempotents, i.e. each $e_i$ is idempotent, $e_ie_j=0$ for $i\neq j$, and $\sum_{i\in\iota}e_i=1$. Assume that $e$ cuts out $f$ in the sense that for every $i\in\iota$ and every prime $x$ of $R$ one has $f(x)=i$ if and only if $e_i\notin x$, and assume the additivity hypothesis that for every prime $y$ of $S$,
--   $$f(\varphi_{12}^{*}y)+f(\varphi_{23}^{*}y)=f(\varphi_{13}^{*}y),$$
--   where $\varphi^{*}$ denotes the map `comap` on prime spectra induced by $\varphi$. The conclusion is that for every $k\in\iota$,
--   $$\sum_{i\in\iota}\varphi_{12}(e_i)\,\varphi_{23}(e_{k-i})=\varphi_{13}(e_k)\qquad\text{in }S.$$
--
--   The statement converts an additive relation between the pullbacks along three ring maps of a locally constant $\iota$-valued function on $\operatorname{Spec}R$ into a convolution relation, in $S$, between the images of the idempotent family cutting out that function. It is used in the descent argument behind [`Algebra.DescentCofaces.exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary`](thm.html#Algebra.DescentCofaces.exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary), where $\varphi_{12},\varphi_{23},\varphi_{13}$ are the three coface maps of an Amitsur (Čech) complex and the hypothesis is the cocycle condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PrimeSpectrum_sum_map_mul_map_eq_map_of_forall_comap_add.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open PrimeSpectrum

theorem PrimeSpectrum.sum_map_mul_map_eq_map_of_forall_comap_add
    {R S : Type*} [CommRing R] [CommRing S] {ι : Type*} [Fintype ι] [AddCommGroup ι]
    (φ₁₂ φ₂₃ φ₁₃ : R →+* S) (f : PrimeSpectrum R → ι) (e : ι → R)
    (he : CompleteOrthogonalIdempotents e)
    (hfe : ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal)
    (hf : ∀ y : PrimeSpectrum S, f (comap φ₁₂ y) + f (comap φ₂₃ y) = f (comap φ₁₃ y)) :
    ∀ k : ι, ∑ i, φ₁₂ (e i) * φ₂₃ (e (k - i)) = φ₁₃ (e k) := by sorry

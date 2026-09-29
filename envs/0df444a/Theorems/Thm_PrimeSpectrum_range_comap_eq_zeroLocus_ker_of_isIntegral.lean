-- Prove2me | Theorems.Thm_PrimeSpectrum_range_comap_eq_zeroLocus_ker_of_isIntegral
-- name    : PrimeSpectrum.range_comap_eq_zeroLocus_ker_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/24b5d1bd-36e0-5398-b3e2-2cc9f099e0cd
-- title:
--   Range of Spec of an integral ring map is V(ker)
-- statement:
--   Let $R$ and $S$ be commutative rings and let $f \colon R \to S$ be a ring homomorphism which is integral, in the sense of `RingHom.IsIntegral`: every element of $S$ is a root of a monic polynomial with coefficients in the image of $f$. The assertion is an equality of subsets of $\operatorname{Spec} R$: the set-theoretic range of the induced map $\operatorname{Spec} S \to \operatorname{Spec} R$, $\mathfrak q \mapsto f^{-1}(\mathfrak q)$, written `PrimeSpectrum.comap f`, coincides with the zero locus of the kernel of $f$, that is with the closed set $V(\ker f)$ of primes of $R$ containing $\ker f$. Equivalently, a prime $\mathfrak p \subseteq R$ is of the form $f^{-1}(\mathfrak q)$ for some prime $\mathfrak q$ of $S$ precisely when $\ker f \subseteq \mathfrak p$. No finiteness, flatness or injectivity hypothesis is imposed on $f$.
--
--   This is the scheme-theoretic form of the lying-over theorem: for an integral ring map the image of the spectrum is exactly the closed subset cut out by the kernel, the spectrum of $R/\ker f$. It is used to identify the ranges of the two chart pieces of a morphism glued from a compatible pair of chart maps in the two-chart integral models of curves, where each chart ring is integral over a subring of the image.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PrimeSpectrum_range_comap_eq_zeroLocus_ker_of_isIntegral.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open PrimeSpectrum

theorem PrimeSpectrum.range_comap_eq_zeroLocus_ker_of_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.IsIntegral) :
    Set.range (PrimeSpectrum.comap f) = PrimeSpectrum.zeroLocus (RingHom.ker f) := by sorry

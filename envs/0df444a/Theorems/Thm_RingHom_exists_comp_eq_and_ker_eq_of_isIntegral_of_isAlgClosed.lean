-- Prove2me | Theorems.Thm_RingHom_exists_comp_eq_and_ker_eq_of_isIntegral_of_isAlgClosed
-- name    : RingHom.exists_comp_eq_and_ker_eq_of_isIntegral_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/4efde1ad-c7db-5417-9523-09a5f1c38c6c
-- title:
--   Extending a point to an algebraically closed field along an integral map
-- statement:
--   Let $B_1$ and $B$ be commutative rings and $\Omega$ an algebraically closed field. Let $f \colon B_1 \to B$ be a ring homomorphism which is integral, in the sense of `RingHom.IsIntegral`: every element of $B$ satisfies a monic polynomial with coefficients in the image of $f$. Let $\varphi_1 \colon B_1 \to \Omega$ be a ring homomorphism, and let $y \subseteq B$ be a prime ideal whose contraction along $f$ is exactly the kernel of $\varphi_1$, i.e. $f^{-1}(y) = \ker \varphi_1$. The conclusion asserts the existence of a ring homomorphism $\varphi \colon B \to \Omega$ with two properties: $\varphi \circ f = \varphi_1$, so that $\varphi$ extends $\varphi_1$ along $f$, and $\ker \varphi = y$ exactly (not merely $y \subseteq \ker \varphi$). Thus an $\Omega$-valued point of $\operatorname{Spec} B_1$ with centre $f^{-1}(y)$ lifts to an $\Omega$-valued point of $\operatorname{Spec} B$ with centre precisely $y$.
--
--   This is the standard extension theorem for homomorphisms into an algebraically closed field along an integral ring map, sharpened to prescribe the kernel of the extension. It is used in the treatment of integral models of modular curves, where a condition imposed on all homomorphisms with a given prime kernel into an algebraically closed field (such as supersingularity of the image of $j$) must be transported between a point and its preimage under a chart map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_exists_comp_eq_and_ker_eq_of_isIntegral_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RingHom.exists_comp_eq_and_ker_eq_of_isIntegral_of_isAlgClosed
    {B₁ B Ω : Type*} [CommRing B₁] [CommRing B] [Field Ω] [IsAlgClosed Ω]
    (f : B₁ →+* B) (hf : f.IsIntegral)
    (φ₁ : B₁ →+* Ω) (y : Ideal B) [y.IsPrime]
    (hy : y.comap f = RingHom.ker φ₁) :
    ∃ φ : B →+* Ω, φ.comp f = φ₁ ∧ RingHom.ker φ = y := by sorry

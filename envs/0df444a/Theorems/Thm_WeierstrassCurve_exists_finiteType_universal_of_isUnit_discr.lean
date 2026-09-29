-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr
-- name    : WeierstrassCurve.exists_finiteType_universal_of_isUnit_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/02a73347-ee20-5fc1-a235-1ba13031416f
-- title:
--   A universal Weierstrass curve with invertible discriminant
-- statement:
--   Let $A$ be a commutative ring, living in a universe $u$. The assertion is that there exist a type $S_0$ in the same universe $u$, a commutative ring structure on $S_0$, an $A$-algebra structure on it for which $S_0$ is of finite type over $A$ (in the sense of `Algebra.FiniteType`, i.e. a quotient of a polynomial ring in finitely many variables over $A$), a Weierstrass curve $W_0$ over $S_0$ — that is, a five-tuple of coefficients $a_1,a_2,a_3,a_4,a_6 \in S_0$ — whose discriminant $\Delta$ is a unit of $S_0$, with the following universal property: for every commutative ring $T$ in the universe $u$ equipped with an $A$-algebra structure and every Weierstrass curve $W$ over $T$ whose discriminant is a unit of $T$, there is exactly one $A$-algebra homomorphism $\psi : S_0 \to T$ such that the coefficientwise image $W_0.\mathrm{map}\,\psi$ of $W_0$ along the underlying ring homomorphism of $\psi$ equals $W$. Equality of Weierstrass curves here is equality of all five coefficients; no smoothness or group-scheme structure is mentioned, only invertibility of $\Delta$.
--
--   This is the representability of the functor of Weierstrass curves with invertible discriminant by the localisation $A[a_1,a_2,a_3,a_4,a_6][\Delta^{-1}]$, the classical universal elliptic curve in Weierstrass form over a base ring $A$. It serves as the Weierstrass stage of the representability statements for full-level moduli data, being cited by [`ModularCurve.FullLevel.Diamond.exists_represents_raw_rigidDataGamma1Pow`](thm.html#ModularCurve.FullLevel.Diamond.exists_represents_raw_rigidDataGamma1Pow), [`ModularCurve.FullLevel.Diamond.exists_represents_raw_trivial_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.exists_represents_raw_trivial_rigidDataH1Pow) and [`ModularCurve.FullLevel.exists_levelModuliPackageAbs_trivial_of_isUnit_two_three_gamma0Pow`](thm.html#ModularCurve.FullLevel.exists_levelModuliPackageAbs_trivial_of_isUnit_two_three_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WeierstrassCurve.exists_finiteType_universal_of_isUnit_discr (A : Type u) [CommRing A] :
    ∃ (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra A S₀) (_ : Algebra.FiniteType A S₀)
      (W₀ : WeierstrassCurve S₀) (_ : IsUnit W₀.Δ),
      ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T), IsUnit W.Δ →
        ∃! ψ : S₀ →ₐ[A] T, W₀.map ψ.toRingHom = W := by sorry

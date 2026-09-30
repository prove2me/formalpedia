-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_senthil_kumar_theorem_one
-- name    : WeierstrassEllipticZeta.senthil_kumar_theorem_one
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-04T23:39:54.388162+00:00
-- url     : https://prove2.me/theorems/2f72029d-c457-4cb8-9516-1ea9eaeaa298
-- title:
--   Theorem 1: Algebraically independent Weierstrass values
-- statement:
--   Let $\Omega$ be the lattice of an arbitrary period pair, with associated Weierstrass functions $\wp,\zeta$ and invariants $g_2,g_3$. Let $\omega\ne0$ be an element of $\Omega$, and let $u_1,u_2\in\mathbb C$ satisfy both
--   $$u_1,u_2,\omega\text{ are linearly independent over }\mathbb Q,$$
--   and
--   $$(\mathbb Zu_1+\mathbb Zu_2)\cap\Omega=\{0\}.$$
--   Then at least two entries of
--   $$\bigl(g_2,g_3,\omega,\eta(\omega),u_1,u_2,\wp(u_1),\zeta(u_1),\wp(u_2),\zeta(u_2)\bigr)$$
--   are algebraically independent over $\mathbb Q$, where $\eta(\omega)=\zeta(\omega_1/2+\omega)-\zeta(\omega_1/2)$ and $\zeta$ is the fixed canonical lattice series. Formally, there exist distinct indices $i,j\in\{0,\ldots,9\}$ for which no nonzero rational polynomial in two variables vanishes at the selected pair. The hypotheses already exclude lattice poles at $u_1,u_2$. No algebraicity hypothesis is added for the invariants, and no particular pair is prescribed. This formalizes the published Theorem 1. Its checked proof has no Open theorem dependencies.
-- source:
--   Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions, Proceedings of the Edinburgh Mathematical Society (online 17 June 2026), §1, Theorem 1, https://doi.org/10.1017/S001309152610145X.

import Definitions.Def_WeierstrassEllipticZeta_Defs

namespace WeierstrassEllipticZeta

/-- Senthil Kumar (2026), Theorem 1. This is an open proof target. -/
theorem senthil_kumar_theorem_one (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω_ne : ω ≠ 0)
    (hω_period : ω ∈ L.lattice)
    (h_linearIndependent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥) :
    HasAlgebraicallyIndependentPair (theoremOneValues L ω u₁ u₂) := by sorry

end WeierstrassEllipticZeta

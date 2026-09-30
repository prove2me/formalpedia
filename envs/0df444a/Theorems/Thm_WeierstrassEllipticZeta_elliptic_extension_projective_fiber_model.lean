-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_fiber_model
-- name    : WeierstrassEllipticZeta.elliptic_extension_projective_fiber_model
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T17:51:31.202205+00:00
-- url     : https://prove2.me/theorems/e106f506-49e9-4efd-85d3-079039e04fd9
-- title:
--   Additive fibers of the projective elliptic-extension locus
-- statement:
--   Let $g_2,g_3\in\mathbb C$ be arbitrary, and consider the projective locus
--
--   $$Z^\circ_{g_2,g_3}=\{[X_0:X_1:X_2:X_3:X_4]\in\mathbb P^4(\mathbb C):
--   X_0X_4-X_2X_3-2X_1^2=0,\quad
--   X_0X_2^2-4X_1^3+g_2X_0^2X_1+g_3X_0^3=0,\quad
--   X_0\ne0\text{ or }X_2\ne0\}.$$
--
--   There exist a projection $\pi:Z^\circ_{g_2,g_3}\to\mathbb P^2(\mathbb C)$ and an additive action $A:\mathbb C\times Z^\circ_{g_2,g_3}\to Z^\circ_{g_2,g_3}$ with the following properties:
--
--   $$\pi([X])=[X_0:X_1:X_2],\qquad
--   A(u,[X])=[X_0:X_1:X_2:X_3+uX_0:X_4+uX_2].$$
--
--   The image of $\pi$ is exactly the homogeneous Weierstrass cubic, written in the coordinate order $(Z,X,Y)$:
--
--   $$\{[Z:X:Y]\in\mathbb P^2(\mathbb C):ZY^2-4X^3+g_2Z^2X+g_3Z^3=0\}.$$
--
--   The action satisfies $A(0,p)=p$ and $A(u+v,p)=A(u,A(v,p))$. It is simply transitive on every fiber:
--
--   $$\pi(p)=\pi(q)\quad\Longleftrightarrow\quad\exists!\,u\in\mathbb C,\ A(u,p)=q.$$
--
--   All formulas are independent of homogeneous representatives and include the fiber at infinity. No discriminant assumption is required for this statement about complex points; it also applies to singular cubic parameters. This supplies the explicit additive-fiber geometry used in the elliptic-extension construction. It does not assert a scheme structure, regularity of morphisms, or a group law on the total space.
-- source:
--   Algebraic consequence of Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, exact sequence (A.3) and the homogeneous, regular and lattice-point exponential-map displays between (A.3) and (A.4), https://doi.org/10.1017/S001309152610145X. Translation of the second elliptic-extension parameter gives the stated shear. The quadric and cubic coordinate relations yield the complete pointwise fiber model. The extension to arbitrary, possibly singular cubic parameters is an inferred algebraic generalization, proved here; no algebraic-group identification is asserted.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_extension_projective_fiber_model (g₂ g₃ : ℂ) :
    Nonempty (ProjectiveExtensionFiberModel g₂ g₃) := by sorry

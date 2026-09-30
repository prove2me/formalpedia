-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_linear_analytic_subgroup_degree_profile
-- name    : WeierstrassEllipticZeta.linear_analytic_subgroup_degree_profile
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T04:49:52.982983+00:00
-- url     : https://prove2.me/theorems/99c6c72e-8d6f-48fb-8904-ae800f4a5cbc
-- title:
--   Projection restriction for polynomially constrained analytic subgroups
-- statement:
--   Let $L$ be a complex period pair and let $V\subset\mathbb C^3$ be a complex linear subspace. For any $\mathbb Z$-linear map $\eta:\Lambda\to\mathbb C$, suppose $H$ is exactly the image of $V$ under
--   $$
--   (t,z,u)\longmapsto (t,[(z,u)])\in\mathbb C\times\bigl(\mathbb C^2/\{(\omega,-\eta(\omega)): \omega\in\Lambda\}\bigr).
--   $$
--   Let $P(T,X,Y,Z)$ be a polynomial that vanishes at
--   $$
--   (t,\wp(z),\wp'(z),u+\zeta(z))
--   $$
--   for every $(t,z,u)\in V$ with $z\notin\Lambda$. Assume that $P(z,\wp(z),\wp'(z),\zeta(z))$ is nonzero at some regular $z$. Then $H$ lies in the kernel of the additive projection or in the kernel of the elliptic projection. More precisely, there is $a\in\{0,1\}$ such that
--   $$
--   m^a=\begin{cases}m&\text{if every }v\in V\text{ has }v_0=0,\\1&\text{otherwise},\end{cases}
--   $$
--   for every real $m$, and the first kernel contains $H$ when $a=1$, while the second contains $H$ when $a=0$.
--
--   The proof uses the period/quasiperiod determinant to saturate the two additive coordinates of each regular elliptic fibre. If $V$ contains $(a,b,c)$ with $ab\ne0$, rescaling this vector gives a line of the form $(\alpha z,z,\beta z)$ with $\alpha\ne0$. Translating $z$ by the two basic periods leaves $\wp(z)$ and $\wp'(z)$ fixed. The changes in the first and fourth polynomial coordinates have determinant
--   $$
--   \alpha\bigl(\omega_1\eta_2-\omega_2\eta_1\bigr)\ne0.
--   $$
--   The resulting polynomial in the two translation indices vanishes on $\mathbb N^2$, hence is the zero polynomial. Invertibility of the displayed matrix then makes $P$ vanish for arbitrary values of the first and fourth coordinates in each regular elliptic fibre. This contradicts the assumed nonzero value on the original curve.
--
--   Consequently each vector of $V$ has either its first or its second coordinate zero. Linearity shows that one of these coordinates vanishes on all of $V$: otherwise adding two vectors supported in the opposite cases gives a vector with both coordinates nonzero. Passing to the quotient gives the asserted projection kernels and the exponent $a$.
--
--   This proves the projection restriction for explicitly parametrized analytic subgroups. It does not assume the restriction as a hypothesis. It also does not assert that an obstruction subgroup with the required uniform degree bound has been constructed. The derivative coordinate is retained throughout; no algebraic independence of $\wp$ and $\wp'$ is asserted.
--
--   Source: Senthil Kumar K, *Algebraic independence of values of Weierstrass elliptic and zeta functions*, Appendix A, §A.2 and Lemma A.1, https://doi.org/10.1017/S001309152610145X. The statement is a concrete analytic projection criterion for that argument, with an explicit linear parametrization hypothesis. The period/quasiperiod determinant proof is reused from the established functional-nonvanishing argument.
-- source:
--   Senthil Kumar K (2026), Appendix A, §A.2, Lemma A.1 and Theorem A.2; https://doi.org/10.1017/S001309152610145X. Concrete analytic subgroup criterion and specialized multiplicity target.

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Mathlib.Algebra.MvPolynomial.Eval
open WeierstrassEllipticZeta TranscendenceTheory MvPolynomial
open scoped Classical

theorem WeierstrassEllipticZeta.linear_analytic_subgroup_degree_profile (L : PeriodPair)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (V : Submodule ℂ (Fin 3 → ℂ))
    (H : Submodule ℤ (GraphExtensionGroup L.lattice η))
    (hH : ∀ g, g ∈ H ↔ ∃ v ∈ V,
      g = (v 0, (extensionPeriodGraph L.lattice η).mkQ (v 1, v 2)))
    (P : MvPolynomial (Fin 4) ℂ)
    (hproper : ∃ z : ℂ, z ∉ L.lattice ∧
      eval ![z, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z] P ≠ 0)
    (hvanish : ∀ v ∈ V, v 1 ∉ L.lattice →
      eval ![v 0, L.weierstrassP (v 1), L.derivWeierstrassP (v 1),
        v 2 + weierstrassZeta L (v 1)] P = 0) :
    ∃ a : ℕ, (∀ m : ℝ, m ^ a = if (∀ v ∈ V, v 0 = 0) then m else 1) ∧
      ((a = 1 ∧ H ≤ LinearMap.ker (extensionAdditiveProjection L.lattice η)) ∨
        (a = 0 ∧ H ≤ LinearMap.ker (extensionEllipticProjection L.lattice η))) := by sorry

-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_quotient_dimension
-- name    : WeierstrassEllipticZeta.elliptic_extension_contact_quotient_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T21:53:17.409283+00:00
-- url     : https://prove2.me/theorems/5a13a853-a529-4d03-8da5-af02648e0c77
-- title:
--   Exact dimensions of contact quotients and arbitrary finite scalar jets
-- statement:
--   For complex parameters $g_2,g_3$, consider the two polynomial derivations on four-variable polynomial rings over $\mathbb C$:
--
--   $$\mathcal D_0=\partial_t+y\partial_x+(6x^2-g_2/2)\partial_y-x\partial_r$$
--
--   in variables $(t,x,y,r)$, and
--
--   $$\mathcal D_2=\partial_t+(-6b^2+g_2a^2/2)\partial_a
--   +(-1/2-g_2ab-3g_3a^2/2)\partial_b
--   +(-2g_2b^2-3g_3ab)\partial_d$$
--
--   in variables $(t,a,b,d)$.
--
--   Let $A=\mathbb C[x_0,x_1,x_2,x_3]$ denote the polynomial ring in either chart's four coordinates. For an affine point $v\in\mathbb C^4$ and an integer $N\ge0$, let
--
--   $$J_{c,v}(N)=\left\langle p\in A:(\mathcal D_c^kp)(v)=0\text{ for every }0\le k<N\right\rangle.$$
--
--   For every fixed $g_2,g_3\in\mathbb C$, either chart, finite set $V\subset\mathbb C^4$ and choice of orders $N_v\ge0$, put
--
--   $$I=\bigcap_{v\in V}J_{c,v}(N_v).$$
--
--   Then $A/I$ is a finite-dimensional complex vector space, with the exact dimension
--
--   $$\dim_{\mathbb C}(A/I)=\sum_{v\in V}N_v.$$
--
--   Moreover, every assignment of complex numbers $a_{v,k}$ for $v\in V$ and $0\le k<N_v$ is realized by a polynomial $p\in A$:
--
--   $$ (\mathcal D_c^kp)(v)=a_{v,k}.$$
--
--   Thus the quotient records precisely these independent scalar jets. In particular, an order-$N$ contact ideal at a single point has quotient dimension $N$.
--
--   The proof uses $\mathcal D_c t=1$ in both charts. At one point, the polynomials $(t-v_0)^i/i!$ give the standard basis of jet data. The proved Chinese remainder property of the contact ideals combines these local polynomials at distinct points. The jet-evaluation map is complex-linear and surjective, its kernel is $I$, and the first isomorphism theorem gives the dimension formula.
--
--   **Formalization Note** The statement includes empty finite sets and zero orders; the empty intersection is the whole ring, whose quotient has dimension zero. The points need not lie on the chart cubic, and no nonsingularity or chart-denominator premise is required. No bound on the degree of the simultaneous interpolating polynomial is asserted. Lean chart indices 0 and 1 select homogeneous-coordinate charts 0 and 2.
-- source:
--   Derived local multiplicity calculation for the one-parameter subgroup and differential polynomial rings of Senthil Kumar K (2026), Appendix A introductory paragraphs, Theorem A.2 and the elliptic-extension curve of Appendix A.2, https://doi.org/10.1017/S001309152610145X. This exact quotient-dimension assertion is proved here and is not quoted as the quantitative zero estimate. The additive coordinate satisfies D(t)=1 in both explicit chart derivations. Taylor monomials and the proved contact-ideal Chinese remainder property give surjective scalar jet evaluation, and the first isomorphism theorem gives dimension equal to the sum of contact orders. Formal references include Mathlib Derivation.comp_aeval_eq, Polynomial.iterate_derivative_X_sub_pow and LinearMap.quotKerEquivOfSurjective.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open WeierstrassEllipticZeta MvPolynomial

theorem WeierstrassEllipticZeta.elliptic_extension_contact_quotient_dimension (g₂ g₃ : ℂ) :
    ∀ (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (n : V → ℕ),
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸
        ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
        ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) = ∑ v : V, n v ∧
      ∀ a : (v : V) → Fin (n v) → ℂ, ∃ p : MvPolynomial (Fin 4) ℂ,
        ∀ (v : V) (k : Fin (n v)),
          eval v.val ((extensionChartDerivation g₂ g₃ c)^[k.val] p) = a v k := by sorry

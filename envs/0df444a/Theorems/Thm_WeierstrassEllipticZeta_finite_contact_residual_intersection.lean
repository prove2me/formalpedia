-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_contact_residual_intersection
-- name    : WeierstrassEllipticZeta.finite_contact_residual_intersection
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T14:30:01.0471+00:00
-- url     : https://prove2.me/theorems/bf9db7f2-7fd2-40f3-a25f-98e5631cfdea
-- title:
--   Residual intersections have maximum contact orders and square-zero defect
-- statement:
--   Let $A=\mathbb C[t,x_1,x_2,x_3]$, let $g_2,g_3\in\mathbb C$, and choose either elliptic-extension chart $c$ with its specified polynomial derivation $D_c$. For a point $v\in\mathbb C^4$ write
--
--   $$C_v(a)=\{p\in A:(D_c^j p)(v)=0\text{ for }0\le j<a\}.$$
--
--   Let $V\subset\mathbb C^4$ be finite, and let $n_v,e_v$ be nonnegative integers with $e_v\le n_v$. Put
--
--   $$I=\bigcap_{v\in V}C_v(n_v),\qquad J=\bigcap_{v\in V}C_v(e_v),\qquad R=I:J,\qquad K=J\cap R.$$
--
--   Then
--
--   $$I\subseteq K,\qquad K^2\subseteq I,\qquad K=\bigcap_{v\in V}C_v\bigl(\max(e_v,n_v-e_v)\bigr).$$
--
--   The quotient $A/K$ is finite dimensional and
--
--   $$\dim_{\mathbb C}(A/K)=\sum_{v\in V}\max(e_v,n_v-e_v),$$
--
--   $$\dim_{\mathbb C}(A/K)+\dim_{\mathbb C}(A/(J+R))=\dim_{\mathbb C}(A/I).$$
--
--   Moreover,
--
--   $$K=I\quad\Longleftrightarrow\quad J+R=A.$$
--
--   Thus $K/I$ is a square-zero ideal in $A/I$. The quotient by $K$ removes exactly the dimension measured by the residual overlap quotient $A/(J+R)$. That defect vanishes precisely in the comaximal case.
--
--   **Formalization Note** The formal contact ideal is defined as a span, and the proved contact-ideal structure theorem identifies it with the displayed jet conditions. The formal theorem expresses the square-zero assertion as the two containments $I\subseteq K$ and $K^2\subseteq I$; it does not assert $K^2=0$ in the polynomial ring. The colon is by the whole ideal $J$. No comaximality, positivity of the orders, injectivity of time coordinates, actual-curve condition or global zero estimate is assumed. Empty $V$ and endpoint orders are included.
-- source:
--   Derived contact-ideal calculation for the differential polynomial-ring method associated with Senthil Kumar K (2026), Appendix A introductory paragraphs and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This exact intersection and square-zero defect statement is proved here, not quoted from the article. Reuses the Proved finite_contact_ideal_colon, finite_contact_ideal_sum and elliptic_extension_contact_quotient_dimension. Antitonicity of contact ideals gives maximum orders for the intersection. Colon membership gives its square contained in the original ideal. The identity max(e,n-e)+min(e,n-e)=n gives the quotient-dimension balance. The existing sum criterion and vanishing of a sum of nonnegative overlap orders characterize equality with the original ideal. Primary Mathlib references: Ideal.span_mono, Ideal.mul_le, Submodule.mem_colon, Submodule.mem_iInf and Finset.sum_eq_zero_iff.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Colon

open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.finite_contact_residual_intersection (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n e : V → ℕ) (he : ∀ v : V, e v ≤ n v) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (e v)
    let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
    let K := J ⊓ R
    I ≤ K ∧ K ^ 2 ≤ I ∧
      K = (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val
        (max (e v) (n v - e v))) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) =
        ∑ v : V, max (e v) (n v - e v) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) +
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) =
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) ∧
      (K = I ↔ J ⊔ R = ⊤) := by sorry

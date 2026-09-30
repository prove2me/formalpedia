-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_contact_ideal_colon
-- name    : WeierstrassEllipticZeta.finite_contact_ideal_colon
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T13:28:36.518976+00:00
-- url     : https://prove2.me/theorems/0e689188-8630-44b6-8384-7b3667076349
-- title:
--   Exact complementary contact orders for colons of finite contact ideals
-- statement:
--   Let $A=\mathbb C[t,x_1,x_2,x_3]$, choose complex parameters $g_2,g_3$, and choose either elliptic-extension chart $c\in\{0,1\}$ with its specified polynomial derivation $D_c$. Its time coordinate satisfies $D_c(t)=1$.
--
--   For $v\in\mathbb C^4$ and $m\ge0$, write
--
--   $$C_v(m)=\{p\in A:\ (D_c^j p)(v)=0\text{ for every }0\le j<m\}$$
--
--   for the contact ideal. Let $V\subset\mathbb C^4$ be finite, and choose integers $n_v,e_v\ge0$ with $e_v\le n_v$ for all $v\in V$. Set
--
--   $$I=\bigcap_{v\in V}C_v(n_v),\qquad
--   J=\bigcap_{v\in V}C_v(e_v).$$
--
--   Then the colon by the whole ideal $J$ has the exact complementary contact orders:
--
--   $$I:J=\{q\in A:qJ\subseteq I\}
--   =\bigcap_{v\in V}C_v(n_v-e_v).$$
--
--   Its quotient is finite dimensional over $\mathbb C$, with
--
--   $$\dim_{\mathbb C}(A/(I:J))=\sum_{v\in V}(n_v-e_v).$$
--
--   This identifies the residual scheme and its length directly from the two sets of contact multiplicities.
--
--   **Formalization Note** The formal contact ideal is defined as the span of the displayed vanishing conditions, and the Proved contact-ideal structure theorem identifies membership with those conditions exactly. The colon is by the entire ideal regarded as a subset, not by one chosen generator. No quotient-length balance, time-polynomial presentation, injectivity of the time coordinates, nonsingularity or actual-curve condition is assumed. Distinct points of $V$ may have the same time coordinate. Empty $V$, zero orders, $e_v=0$ and $e_v=n_v$ are included. The result asserts no global zero estimate.
-- source:
--   Derived contact-ideal calculation for the differential polynomial-ring method in Senthil Kumar K (2026), Appendix A introductory paragraphs and the multiplicity hypotheses of Theorem A.2, specialized to the chart derivations of Appendix A.2, https://doi.org/10.1017/S001309152610145X. This exact colon formula is proved here, not quoted from the article. The identity D(t)=1 gives cancellation of a centered time factor in a contact ideal. Chinese remainder interpolation produces a test polynomial equal to a centered time power modulo the chosen contact ideal and zero modulo the others. Testing colon membership on this polynomial forces the complementary contact order. The converse uses multiplication of contact ideals. The Proved contact-quotient dimension theorem computes the length. Primary formal references: Derivation.leibniz, Function.iterate_succ_apply, Ideal.pow_mem_pow, Submodule.mem_colon and the Proved elliptic_extension_contact_ideal_structure and elliptic_extension_contact_quotient_dimension.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Colon

open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.finite_contact_ideal_colon (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n e : V → ℕ) (he : ∀ v : V, e v ≤ n v) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (e v)
    let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
    R = (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v - e v)) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) = ∑ v : V, (n v - e v) := by sorry

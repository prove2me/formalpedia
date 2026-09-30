-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_residual_contact_ideal_decomposition
-- name    : WeierstrassEllipticZeta.residual_contact_ideal_decomposition
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T03:05:04.18542+00:00
-- url     : https://prove2.me/theorems/527d09fd-c74c-4c72-be73-4cd7d9a37856
-- title:
--   Residual contact ideal decomposition from complementary length
-- statement:
--   Write $A=\mathbb C[t,x_1,x_2,x_3]$. Fix arbitrary chart parameters $g_2,g_3\in\mathbb C$ and a chart $c\in\{0,1\}$, with its derivation $D_c$. For a point $v\in\mathbb C^4$ and an integer $a\ge0$, let
--
--   $$C_c(v,a)=\{f\in A:(D_c^j f)(v)=0\text{ for every }0\le j<a\}.$$
--
--   Let $V\subset\mathbb C^4$ be finite. Choose orders $n_v,e_v\in\mathbb N$ with $e_v\le n_v$ for each $v\in V$, and a polynomial $p\in A$ such that
--
--   $$(D_c^j p)(v)=0\qquad(v\in V,\ 0\le j<e_v).$$
--
--   Set
--
--   $$I=\bigcap_{v\in V}C_c(v,n_v),\qquad R=I:p=\{f\in A:fp\in I\}.$$
--
--   Assume the residual length balance
--
--   $$\operatorname{finrank}_{\mathbb C}(A/R)+\sum_{v\in V}e_v=\sum_{v\in V}n_v.$$
--
--   Then the residual ideal has the exact complementary contact decomposition
--
--   $$R=\bigcap_{v\in V}C_c(v,n_v-e_v).$$
--
--   Moreover $A/R$ is finite dimensional over $\mathbb C$ and
--
--   $$\dim_{\mathbb C}(A/R)=\sum_{v\in V}(n_v-e_v).$$
--
--   **Formalization Note** The scalar length balance is a hypothesis, and only the displayed lower bounds on the vanishing orders of $p$ are assumed. The proof obtains finite dimensionality from the complementary contact ideal and its inclusion in $R$, so no separate finite-dimensionality premise is needed. Mathlib's `Module.finrank` denotes the finite rank used in the balance. The chart and its derivation are exactly those of `ProjectiveContactIdeal`. Empty sets, zero orders, $p=0$, and points sharing a first coordinate are allowed. There is no time-presentation, lattice or nonsingularity hypothesis. The result is a local ideal identity and length calculation; it does not assert a global zero estimate.
-- source:
--   Derived local residual-ideal calculation for the contact-algebra approach associated with Senthil Kumar K (2026), Appendix A, https://doi.org/10.1017/S001309152610145X. This exact statement is proved here, not quoted from the article. The Proved contact structure theorem gives inclusion of the complementary contact ideal in I:p, and the Proved contact quotient dimension theorem computes its colength. The explicitly assumed residual length balance forces equality by injectivity of a surjective linear map between spaces of equal finite dimension. Primary formal references: Ideal.quotientMapₐ, FiniteDimensional.of_surjective, LinearMap.injective_iff_surjective_of_finrank_eq_finrank, Ideal.Quotient.eq_zero_iff_mem and Submodule.mem_colon_singleton.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Colon

open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.residual_contact_ideal_decomposition (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n e : V → ℕ) (he : ∀ v : V, e v ≤ n v)
    (p : MvPolynomial (Fin 4) ℂ)
    (hvan : ∀ (v : V) (j : ℕ), j < e v →
      MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[j] p) = 0) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    let R := I.colon {p}
    (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) + ∑ v : V, e v = ∑ v : V, n v) →
      R = (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v - e v)) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) = ∑ v : V, (n v - e v) := by sorry

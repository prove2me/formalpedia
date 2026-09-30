-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_contact_ideal_sum
-- name    : WeierstrassEllipticZeta.finite_contact_ideal_sum
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T13:43:12.002986+00:00
-- url     : https://prove2.me/theorems/d3268e2f-ef9b-4dff-b4a5-98f86a45a8bd
-- title:
--   Sums of finite contact ideals, intersection lengths and comaximality
-- statement:
--   Let $A=\mathbb C[t,x_1,x_2,x_3]$, choose complex parameters $g_2,g_3$, and choose either elliptic-extension chart $c\in\{0,1\}$ with its specified polynomial derivation $D_c$. For $v\in\mathbb C^4$ and $a\ge0$, let
--
--   $$C_v(a)=\{p\in A:(D_c^j p)(v)=0\text{ for every }0\le j<a\}$$
--
--   be the contact ideal. Let $V\subset\mathbb C^4$ be finite and let $m_v,n_v\ge0$ be arbitrary integers. Put
--
--   $$I=\bigcap_{v\in V}C_v(m_v),\qquad
--   J=\bigcap_{v\in V}C_v(n_v).$$
--
--   Then
--
--   $$I+J=\bigcap_{v\in V}C_v(\min(m_v,n_v)).$$
--
--   The quotient $A/(I+J)$ is finite dimensional over $\mathbb C$, and
--
--   $$\dim_{\mathbb C}(A/(I+J))=\sum_{v\in V}\min(m_v,n_v).$$
--
--   Moreover,
--
--   $$I+J=A\quad\Longleftrightarrow\quad
--   \text{for every }v\in V,\quad m_v=0\text{ or }n_v=0.$$
--
--   Thus the contact multiplicities of the scheme intersection are the pointwise minimum, and the two ideals are comaximal precisely when their supports are disjoint.
--
--   **Formalization Note** The formal contact ideal is the span of the displayed vanishing conditions; its Proved membership theorem identifies it exactly with that set. The symbol `⊔` is ideal sum. The two order functions need not be comparable. There is no assumed length formula, global time presentation, injective time coordinate, nonsingularity or actual-curve hypothesis. Empty $V$ and zero orders are included; an empty intersection and a zero-order contact ideal are the whole ring. The result asserts no global zero estimate.
-- source:
--   Derived contact-ideal calculation for the differential polynomial-ring method in Senthil Kumar K (2026), Appendix A introductory paragraphs and the multiplicity hypotheses of Theorem A.2, specialized to the chart derivations of Appendix A.2, https://doi.org/10.1017/S001309152610145X. This exact ideal-sum formula is proved here, not quoted from the article. Contact membership gives monotonicity of the local ideals. Chinese remainder interpolation modulo the maximum contact orders splits an arbitrary polynomial of the minimum contact orders into a member of each original ideal. The Proved contact-quotient dimension theorem computes the quotient length. Testing the constant polynomial 1 identifies exactly when the sum is the whole ring. Primary formal references: Submodule.mem_sup, Submodule.mem_iInf and the Proved elliptic_extension_contact_ideal_structure and elliptic_extension_contact_quotient_dimension.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Operations

open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.finite_contact_ideal_sum (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (m n : V → ℕ) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (m v)
    let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    I ⊔ J = (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (min (m v) (n v))) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ I ⊔ J) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I ⊔ J) =
        ∑ v : V, min (m v) (n v) ∧
      (I ⊔ J = ⊤ ↔ ∀ v : V, m v = 0 ∨ n v = 0) := by sorry

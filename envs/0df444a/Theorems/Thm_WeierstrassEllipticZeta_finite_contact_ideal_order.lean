-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_contact_ideal_order
-- name    : WeierstrassEllipticZeta.finite_contact_ideal_order
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T14:45:21.772198+00:00
-- url     : https://prove2.me/theorems/e5b0bb0f-6344-41db-a2c9-f9bc5b038459
-- title:
--   Inclusion, equality and strict inclusion of finite contact ideals
-- statement:
--   Let $A=\mathbb C[t,x_1,x_2,x_3]$, choose complex parameters $g_2,g_3$,
--   and choose either elliptic-extension chart with its polynomial derivation
--   $D_c$. For $v\in\mathbb C^4$ and $a\ge0$, let
--
--   $$C_v(a)=\{p\in A:(D_c^j p)(v)=0\text{ for every }0\le j<a\}.$$
--
--   Let $V\subset\mathbb C^4$ be finite, and let $m,n:V\to\mathbb N$ be
--   arbitrary. Set
--
--   $$I_m=\bigcap_{v\in V}C_v(m_v),\qquad
--   I_n=\bigcap_{v\in V}C_v(n_v).$$
--
--   Then inclusion is characterized by the reverse pointwise order:
--
--   $$I_m\subseteq I_n\quad\Longleftrightarrow\quad
--   n_v\le m_v\text{ for every }v\in V.$$
--
--   Equality determines the entire multiplicity function:
--
--   $$I_m=I_n\quad\Longleftrightarrow\quad m=n.$$
--
--   Finally,
--
--   $$I_m\subsetneq I_n\quad\Longleftrightarrow\quad
--   \bigl(\forall v\in V,\ n_v\le m_v\bigr)
--   \ \text{and}\ \bigl(\exists v\in V,\ n_v<m_v\bigr).$$
--
--   Thus a finite contact ideal determines its orders uniquely on the fixed
--   finite set, and ideal comparisons are exactly numerical comparisons of
--   those orders.
--
--   **Formalization Note** The formal contact ideals are defined as spans;
--   the proved structure theorem identifies membership with the displayed
--   jet conditions. The two multiplicity functions have no positivity,
--   comparability or upper-bound assumption. The finite set may be empty,
--   orders may be zero, and distinct full affine points may have the same
--   time coordinate. The result concerns the stated family of contact
--   ideals on a fixed $V$.
-- source:
--   Derived contact-ideal order calculation for the differential polynomial-ring method associated with Senthil Kumar K (2026), Appendix A introductory paragraphs and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This exact order characterization is proved here, not quoted from the article. Reuses the Proved finite_contact_ideal_sum and elliptic_extension_contact_quotient_dimension. Inclusion makes the ideal sum equal its larger member; comparing the minimum-order dimension formula with the dimension of that member forces every multiplicity inequality. Reverse inclusion follows from the span definition. Antisymmetry gives uniqueness, and strict inclusion is inclusion without reverse inclusion. Primary formal references: Ideal.span_mono, Submodule.mem_iInf, sup_eq_right, Finset.sum_lt_sum and lt_iff_le_not_ge.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Colon

open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.finite_contact_ideal_order (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (m n : V → ℕ) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (m v)
    let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    (I ≤ J ↔ ∀ v : V, n v ≤ m v) ∧
      (I = J ↔ m = n) ∧
      (I < J ↔ (∀ v : V, n v ≤ m v) ∧ ∃ v : V, n v < m v) := by sorry

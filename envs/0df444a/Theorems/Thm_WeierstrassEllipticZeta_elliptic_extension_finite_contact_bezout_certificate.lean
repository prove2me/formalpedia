-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_finite_contact_bezout_certificate
-- name    : WeierstrassEllipticZeta.elliptic_extension_finite_contact_bezout_certificate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T23:48:06.405718+00:00
-- url     : https://prove2.me/theorems/b41d7142-2376-4c76-97d7-11aa19d80b07
-- title:
--   Bézout certificates in finite elliptic-extension contact quotients
-- statement:
--   Fix complex numbers $g_2,g_3$, one of the two elliptic-extension charts, and a finite set $V$ of affine points in $\mathbb C^4$. Write $A=\mathbb C[t,x_1,x_2,x_3]$. Assign each $v\in V$ a natural contact order $n_v$, let $J_v=J_v(n_v)$ be its chart contact ideal, and put
--
--   $$I=\bigcap_{v\in V}J_v.$$
--
--   Assume two established properties of the contact ideals. First, if $\mathfrak m_v$ is the kernel of evaluation at $v$, then
--
--   $$\mathfrak m_v^{n_v}\subseteq J_v.$$
--
--   Second, every family $p_v\in A$ admits a simultaneous representative: there exists $q\in A$ such that $q-p_v\in J_v$ for every $v\in V$.
--
--   Let $f_0,\ldots,f_{K-1}\in A$ be a finite family. Assume that at each point of positive contact order, at least one of these polynomials is nonzero:
--
--   $$n_v>0\quad\Longrightarrow\quad \exists j<K,\ f_j(v)\ne0.$$
--
--   Then there are polynomials $a_0,\ldots,a_{K-1}\in A$ satisfying the finite Bézout certificate
--
--   $$1-\sum_{j<K}a_jf_j\in I.$$
--
--   Moreover,
--
--   $$I+(f_0,\ldots,f_{K-1})=A.$$
--
--   Thus these equations generate the unit ideal in the contact quotient: after imposing all of them, no contact contribution remains, including nilpotent multiplicity.
--
--   **Formalization Note** The power containment and simultaneous-representative property are explicit hypotheses, both supplied by the proved contact-ideal structure. Distinct time coordinates are not required. The contact orders may vary and may be zero; no nonvanishing condition is imposed at order zero. Empty point sets and empty polynomial families are covered whenever the displayed hypotheses hold. The result asserts existence of polynomial coefficients, with no degree bound on those coefficients. In the mission reduction, the family consists of the derivatives of the normalized polynomial of orders strictly below the existing cutoff $B(m+2n)$. This is a finite contact-algebra certificate, not the global quantitative zero estimate.
-- source:
--   Derived finite contact-algebra lemma for the approach in Senthil Kumar K (2026), Appendix A and Appendix A.2, https://doi.org/10.1017/S001309152610145X. Proved here from the explicit contact power containment and Chinese remainder hypotheses; it is not quoted as Theorem A.2. Primary formal references: Mathlib geom_sum_mul_neg, Ideal.pow_mem_pow, Submodule.mem_iInf, Submodule.sum_mem, Ideal.mul_mem_right, Ideal.mul_mem_left and Ideal.eq_top_iff_one.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.elliptic_extension_finite_contact_bezout_certificate
    (g₂ g₃ : ℂ) (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (n : V → ℕ)
    (hpower : ∀ v : V, RingHom.ker (MvPolynomial.eval v.val) ^ n v ≤
      extensionChartContactIdeal g₂ g₃ c v.val (n v))
    (hcrt : ∀ p : V → MvPolynomial (Fin 4) ℂ,
      ∃ q : MvPolynomial (Fin 4) ℂ, ∀ v : V,
        q - p v ∈ extensionChartContactIdeal g₂ g₃ c v.val (n v))
    (K : ℕ) (f : Fin K → MvPolynomial (Fin 4) ℂ)
    (hnonzero : ∀ v : V, 0 < n v → ∃ j : Fin K, MvPolynomial.eval v.val (f j) ≠ 0) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    ∃ a : Fin K → MvPolynomial (Fin 4) ℂ,
      1 - ∑ j : Fin K, a j * f j ∈ I ∧ I ⊔ Ideal.span (Set.range f) = ⊤ := by sorry

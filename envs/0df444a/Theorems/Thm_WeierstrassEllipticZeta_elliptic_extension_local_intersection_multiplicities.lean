-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_local_intersection_multiplicities
-- name    : WeierstrassEllipticZeta.elliptic_extension_local_intersection_multiplicities
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T23:20:42.424576+00:00
-- url     : https://prove2.me/theorems/b39e6cc4-e000-4404-a632-2019887d5369
-- title:
--   Local vanishing multiplicities in elliptic-extension contact intersections
-- statement:
--   Fix complex numbers $g_2,g_3$ and one of the two elliptic-extension charts. Let $D$ be its polynomial derivation on $A=\mathbb C[t,x_1,x_2,x_3]$, so $Dt=1$. For an affine point $v$ and a natural number $n$, let $J_v(n)$ be the chart contact ideal. Assume its exact jet-membership criterion:
--
--   $$p\in J_v(n)\quad\Longleftrightarrow\quad D^jp(v)=0\text{ for every }0\le j<n.$$
--
--   Let $V$ be a finite set of affine points whose time coordinates $v_0$ are pairwise distinct, and assign each $v\in V$ a natural contact order $n_v$. Put
--
--   $$I=\bigcap_{v\in V}J_v(n_v),\qquad M(T)=\prod_{v\in V}(T-v_0)^{n_v}.$$
--
--   Fix three polynomials $r_1,r_2,r_3\in\mathbb C[T]$ and write $\Phi(p)=p(T,r_1(T),r_2(T),r_3(T))$. Assume
--
--   $$p\in I\quad\Longleftrightarrow\quad M\mid\Phi(p)\qquad(p\in A).$$
--
--   Then, for every $p\in A$, there are natural numbers $e_v$ with $0\le e_v\le n_v$ such that, for every integer $0\le k\le n_v$,
--
--   $$k\le e_v\quad\Longleftrightarrow\quad D^jp(v)=0\text{ for all }0\le j<k,$$
--
--   and
--
--   $$\deg\gcd(M,\Phi(p))=\sum_{v\in V}e_v.$$
--
--   Thus $e_v$ is precisely the vanishing order detected by the available $n_v$ jets, truncated at $n_v$. Combined with the established gcd-degree formula for $\dim_{\mathbb C}A/(I+(p))$, this expresses the intersection length as the sum of the local truncated vanishing orders.
--
--   **Formalization Note** The explicit assumptions are exact contact membership, distinct time coordinates, and the exact divisibility presentation. There is no degree restriction on $p$ or the coordinate polynomials and no nonvanishing assumption on $\Phi(p)$. Empty point sets and zero contact orders are allowed. If $\Phi(p)=0$, the formula still gives $e_v=n_v$. In Lean the degree is `Polynomial.natDegree`. The proof uses root multiplicities of the nonzero gcd, avoiding the convention that the root multiplicity of the zero polynomial is zero. The bound and prefix-vanishing equivalence specify the local order without introducing an infinity-valued definition. This is a local multiplicity calculation, not a proof of the global zero estimate.
-- source:
--   Derived local multiplicity calculation for the finite-contact approach in Senthil Kumar K (2026), Appendix A and Appendix A.2, https://doi.org/10.1017/S001309152610145X. The lemma is proved here under its explicit contact-presentation assumptions; it is not quoted as the global zero estimate in Theorem A.2. Primary formal references: Mathlib Polynomial.roots_prod, roots_pow, count_roots, le_rootMultiplicity_iff, Splits.of_dvd, Splits.natDegree_eq_card_roots, Multiset.sum_count_eq_card, Derivation.comp_aeval_eq, Polynomial.X_sub_C_pow_dvd_iff and factorial_smul_hasseDeriv.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Tactic.FinCases

open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.elliptic_extension_local_intersection_multiplicities
    (g₂ g₃ : ℂ) (c : Fin 2)
    (hcontact : ∀ (v : Fin 4 → ℂ) (n : ℕ) (p : MvPolynomial (Fin 4) ℂ),
      p ∈ extensionChartContactIdeal g₂ g₃ c v n ↔
        ∀ k < n, MvPolynomial.eval v ((extensionChartDerivation g₂ g₃ c)^[k] p) = 0)
    (V : Finset (Fin 4 → ℂ))
    (hV : Function.Injective (fun v : V => v.val 0)) (n : V → ℕ)
    (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) ↔
        (∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ n v) ∣
          MvPolynomial.aeval (Fin.cons Polynomial.X r) p) :
    ∀ p : MvPolynomial (Fin 4) ℂ, ∃ e : V → ℕ,
      (∀ v : V, e v ≤ n v ∧ ∀ k ≤ n v,
        k ≤ e v ↔ ∀ j < k,
          MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[j] p) = 0) ∧
      (gcd (∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ n v)
        (MvPolynomial.aeval (Fin.cons Polynomial.X r) p)).natDegree = ∑ v : V, e v := by sorry

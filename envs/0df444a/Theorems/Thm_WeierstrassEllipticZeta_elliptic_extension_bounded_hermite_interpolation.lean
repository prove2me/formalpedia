-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_bounded_hermite_interpolation
-- name    : WeierstrassEllipticZeta.elliptic_extension_bounded_hermite_interpolation
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T22:14:46.08963+00:00
-- url     : https://prove2.me/theorems/20ad754f-4a6a-45a2-a323-9c692a5f3f83
-- title:
--   Sharp Hermite interpolation for elliptic-extension chart jets
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
--   Write $t=x_0$ for the independent time coordinate, so that $\mathcal D_c t=1$ in either chart. Fix complex parameters $g_2,g_3$, either chart, a finite set $V\subset\mathbb C^4$, and nonnegative integers $N_v$ for $v\in V$. Assume the first-coordinate map $v\mapsto v_0$ is injective on $V$. Set $\ell=\sum_{v\in V}N_v$.
--
--   For every assignment of complex scalar jets $a_{v,k}$, with $v\in V$ and $0\le k<N_v$, there is a unique univariate polynomial $P\in\mathbb C[T]$ such that
--
--   $$\deg P<\ell,\qquad (\mathcal D_c^k(P(t)))(v)=a_{v,k}.$$
--
--   Here $P(t)$ is the four-variable polynomial obtained by substituting $x_0$ for $T$. Thus all contact data can be interpolated using only the time coordinate, with the sharp degree bound $\ell-1$ when $\ell>0$. Uniqueness is among time polynomials with degree below $\ell$.
--
--   The proof identifies the displayed jets with ordinary derivatives of $P$ at the distinct scalars $v_0$. Taylor expansion characterizes order-$N_v$ vanishing by divisibility by $(T-v_0)^{N_v}$. The Chinese remainder theorem supplies a simultaneous interpolant, and its remainder modulo $\prod_v(T-v_0)^{N_v}$ has degree below $\ell$. Any two such remainders differ by a multiple of that monic degree-$\ell$ polynomial and hence are equal.
--
--   **Formalization Note** The polynomial degree in this statement is Lean's `Polynomial.degree`, valued in the natural numbers with a bottom element, so the zero polynomial has degree minus infinity. In particular, empty $V$ and zero orders are included: when $\ell=0$, the unique polynomial is zero. Distinct first coordinates are essential to this time-only assertion. No chart-cubic equation, nonzero denominator or nonsingularity condition is required. Lean chart indices 0 and 1 select homogeneous-coordinate charts 0 and 2.
-- source:
--   Derived degree-controlled local interpolation lemma for the differential polynomial rings and one-parameter subgroup in Senthil Kumar K (2026), Appendix A and Appendix A.2, https://doi.org/10.1017/S001309152610145X. This assertion is proved here using the independent additive coordinate D(t)=1 and is not quoted as the quantitative zero estimate of Theorem A.2. Formal primary references: Mathlib Polynomial.taylor_coeff, Polynomial.factorial_smul_hasseDeriv, Polynomial.X_sub_C_pow_dvd_iff, Polynomial.pairwise_coprime_X_sub_C, Ideal.exists_forall_sub_mem_ideal, and Polynomial.degree_modByMonic_lt.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartCalculus
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Defs

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_extension_bounded_hermite_interpolation (g₂ g₃ : ℂ) :
    ∀ (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (n : V → ℕ),
      Function.Injective (fun v : V => v.val 0) →
      ∀ a : (v : V) → Fin (n v) → ℂ, ∃! p : Polynomial ℂ,
        p.degree < (∑ v : V, n v : ℕ) ∧
        ∀ (v : V) (k : Fin (n v)),
          MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[k.val]
            (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) p)) = a v k := by sorry

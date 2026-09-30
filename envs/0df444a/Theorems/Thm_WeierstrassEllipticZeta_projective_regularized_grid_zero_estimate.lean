-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_projective_regularized_grid_zero_estimate
-- name    : WeierstrassEllipticZeta.projective_regularized_grid_zero_estimate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T14:19:50.14953+00:00
-- url     : https://prove2.me/theorems/d9ffbb72-8214-4b6c-baf2-fffbbd61a898
-- title:
--   Zero estimate for the entire projective elliptic curve
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and functions $\wp,\wp',\zeta$. Fix $\omega,u_1,u_2\in\mathbb C$ satisfying `RegularAuxiliaryGridData`: the integer map $J(a,b,c)=au_1+bu_2+c\omega$ is injective, lies in $\Lambda$ exactly when $a=b=0$, and two integer grid points are congruent modulo $\Lambda$ exactly when their first two coordinates agree. Every $J(a,b,c)+u_1/2$ is regular. The data includes the standard finite-grid cardinalities, shifted-grid radius bounds and period-translation formulas.
--
--   Let $\sigma$ be normalized entire sigma differential data for $L$. Suppose $S_0,\ldots,S_4$ are entire functions having no common zero and satisfying, off $\Lambda$,
--
--   $$ (S_0,S_1,S_2,S_3,S_4)=\sigma^3(1,\wp,\wp',\zeta,\wp'\zeta+2\wp^2). $$
--
--   For nonnegative integers $a,b,c$ write
--
--   $$\Gamma(a,b,c)=\{iu_1+ju_2+k\omega:0\le i<a,\ 0\le j<b,\ 0\le k<c\},$$
--
--   where the indices are integers. There is a real $C>0$ with the following property. For all positive integers $m,\ell,s,q$ with $s\le q$ and $\ell\le m$, and every integer $T\ge3$ satisfying
--
--   $$3C\max\{m(15\ell)^2,q(15\ell)^2\}<Ts^2q,$$
--
--   let $Q\in\mathbb C[Y_0,Y_1,X_0,X_1,X_2,X_3,X_4]$ be bihomogeneous of degrees $m,5\ell$. Thus every monomial with nonzero coefficient has total $Y$ degree $m$ and total $X$ degree $5\ell$. Set
--
--   $$H_Q(z)=Q\big(1,z;S_0(z),S_1(z),S_2(z),S_3(z),S_4(z)\big).$$
--
--   If $H_Q$ is not identically zero, there are $v\in\Gamma(3s,3s,3q)$ and an integer $0\le n\le T$ for which $H_Q^{(n)}(v)\ne0$.
--
--   The constant is uniform in all five integer parameters and in $Q$. The function $H_Q$ is entire because its coordinates are entire; no separate extension function is an input. The hypothesis is nonvanishing of the evaluated function, not merely $Q\ne0$. The last coordinate may occur in $Q$. This is the remaining geometric zero estimate for the globally defined projective curve, and still requires proof.
-- source:
--   Senthil Kumar K (2026), Appendix A.2-A.3, Proposition A.1 and the proof of Lemma 9, https://doi.org/10.1017/S001309152610145X. This inferred specialization of the algebraic-group zero estimate uses the entire nonvanishing sigma-cubed lift of phi(z)=exp_G(z,z,0), bidegree (m,5ell), and the existing sufficient finite-grid inequality. The group structure, subgroup classification, multiplicity estimate and grid specialization remain obligations; the parent reduction only identifies its given entire G with the explicit polynomial evaluation.

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.projective_regularized_grid_zero_estimate
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = 5 * l) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
          ∃ n : ℕ, n ≤ T ∧ iteratedDeriv n
            (fun z : ℂ => MvPolynomial.eval
              ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) v ≠ 0 := by sorry

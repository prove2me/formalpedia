-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_auxiliary_polynomial_of_grid_matrices
-- name    : WeierstrassEllipticZeta.bounded_auxiliary_polynomial_of_grid_matrices
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T00:17:59.666045+00:00
-- url     : https://prove2.me/theorems/aac13578-1e0f-4e7c-9e4e-62a45311b012
-- title:
--   Bounded nonzero auxiliary coefficients from grid matrices
-- statement:
--   Let $L$ be a complex period pair and let $\omega,u_1,u_2,\theta,\nu\in\mathbb C$. Let $g\in\mathbb Z[X,Y]$ have positive $Y$-degree $e$, and let $d\in\mathbb Z[X]$. Assume that for every integer bivariate polynomial $p$,
--   $$p(\theta,\nu)=0\quad\Longleftrightarrow\quad g\mid p.$$
--   Assume the bounded grid-matrix package `AuxiliaryGridJetMatrixData` for these data. With
--   $$m=\lfloor N/\log N\rfloor,\quad \ell=\lfloor\sqrt{N\log N}\rfloor,\quad
--   s=\lfloor N^{3/16}\rfloor,\quad q=\lfloor N^{5/8}\log N/64\rfloor,$$
--   this package supplies, for each fixed multiplier $K$, uniformly bounded polynomial matrices on $\Gamma(3s,3s,3q)$ through order $Km$, with $Y$-degree below $e$, $X$-degree at most $D\le Am$, length at most $e^{AN}$, size envelope $|I|(e+1)(D+1)\le e^{AN}$, and the gap $8(m+1)|\Gamma(s,s,q)|\le |I|$, where $I=\{0,\ldots,m\}\times\{0,\ldots,\ell\}^2$. Their common evaluated kernels at a point are exactly the vanishing of the corresponding ordinary monomial derivatives through order $Km$ at $u_1/2+v$. The package also contains nonzero-denominator presentations of all eight fixed/moving coordinates, their degree and length bounds, and the exact period-cleared and nonperiod-cleared entry evaluations. Matrices and presentations precede coefficient vectors.
--
--   There is $C>0$ such that for every sufficiently large $N$ one can choose $p_i\in\mathbb Z[X,Y]$, $i\in I$, with
--   $$\bigl(p_i(\theta,\nu)\bigr)_{i\in I}\ne0,\qquad
--   \deg_Yp_i<e,\quad\deg_Xp_i\le Cm,\quad H(p_i)\le e^{CN},$$
--   and
--   $$\forall v\in\Gamma(s,s,q)\ \forall n\le m,\quad
--   \left(\frac{d^n}{dw^n}\sum_{i\in I}p_i(\theta,\nu)w^{i_0}\wp(w)^{i_1}\zeta(w)^{i_2}\right)_{w=u_1/2+v}=0.$$
--   Here the coefficient bounds quantify over every integer coefficient, including coefficients outside the support, and zero polynomial representatives are permitted. The vector after evaluation must be nonzero. No separate regular-grid, transcendence, monicity or denominator-nonvanishing hypothesis is imposed beyond the evaluation-kernel and grid-matrix assumptions. In particular, no geometric zero estimate is assumed. This is the coefficient-selection step in the proof of Lemma 8, with its matrix construction separated out.
-- source:
--   Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, https://doi.org/10.1017/S001309152610145X, §5, Lemmas 7–8 and equation (29); mission Lemma 8 formal-grid variant with factor 1/64.

import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Mathlib.RingTheory.Algebraic.Defs

open scoped Polynomial
open Filter WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.bounded_auxiliary_polynomial_of_grid_matrices
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ) (g : ℤ[X][X]) (d : ℤ[X])
    (hg : 0 < g.natDegree)
    (hker : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
    (hmat : AuxiliaryGridJetMatrixData L ω u₁ u₂ θ ν g d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      ∃ p : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℤ[X][X],
        (fun i => (p i).eval₂ (Polynomial.aeval θ).toRingHom ν) ≠ 0 ∧
        (∀ i, (p i).natDegree < g.natDegree) ∧
        (∀ i j, (((p i).coeff j).natDegree : ℝ) ≤ C * m) ∧
        (∀ i j k, ‖((p i).coeff j).coeff k‖ ≤ Real.exp (C * N)) ∧
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N],
          ∀ n ≤ m, iteratedDeriv n (fun w => ∑ i,
            (p i).eval₂ (Polynomial.aeval θ).toRingHom ν * w ^ i.1.val *
              L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
                (u₁ / 2 + v) = 0 := by sorry

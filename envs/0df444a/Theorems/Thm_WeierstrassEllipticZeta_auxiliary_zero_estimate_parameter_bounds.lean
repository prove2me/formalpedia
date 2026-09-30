-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_auxiliary_zero_estimate_parameter_bounds
-- name    : WeierstrassEllipticZeta.auxiliary_zero_estimate_parameter_bounds
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T01:38:15.517915+00:00
-- url     : https://prove2.me/theorems/85ed21cb-cd2f-4882-8932-7361aa023b0c
-- title:
--   Auxiliary parameters satisfy the zero-estimate inequalities
-- statement:
--   For each integer $N\ge0$, define
--
--   $$m=\lfloor N/\log N\rfloor,\quad \ell=\lfloor\sqrt{N\log N}\rfloor,\quad
--   s=\lfloor N^{3/16}\rfloor,\quad q=\lfloor N^{5/8}\log N/64\rfloor,$$
--
--   where floors are natural-number floors. For every real $C>0$, there is an integer $k\ge3$ such that, for every sufficiently large $N$,
--
--   $$m,\ell,s,q\ge1,\qquad s\le q\le m,\qquad \ell\le m,\qquad km\ge3,$$
--
--   and
--
--   $$3C\max\{m(15\ell)^2,\ q(15\ell)^2\}<km\,s^2q.$$
--
--   All constants and the threshold are independent of any polynomial coefficients or grid points. In particular, the order $T=km$ satisfies both numerical conditions for the rank-one lattice-intersection zero estimate when the translated polynomial has ordinary degree at most $m$ and elliptic-coordinate degrees at most $5\ell$. The additional loss $6\ell$ is bounded by $6m$.
--
--   This theorem concerns the explicit parameters and their inequalities only; it assumes no zero estimate. One may choose any natural $k>691200C+3$.
-- source:
--   Senthil Kumar K (2026), Section 5, the numerical estimates in the proof of Lemma 9 and the rank-one case of Appendix Proposition A.1, https://doi.org/10.1017/S001309152610145X. The constants 15, 3, and the loss 6 correspond to cleared translation and the T>=3 zero estimate. The explicit sufficient choice k>691200C+3 and the floor inequalities are a derived quantitative formulation, not quoted constants from the article.

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryParameters

open Filter WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.auxiliary_zero_estimate_parameter_bounds (C : ℝ) (hC : 0 < C) :
    ∃ k : ℕ, 3 ≤ k ∧ ∀ᶠ N : ℕ in atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let s := auxiliaryS N
      let q := auxiliaryS3 N
      1 ≤ m ∧ 1 ≤ l ∧ 1 ≤ s ∧ 1 ≤ q ∧ s ≤ q ∧ q ≤ m ∧ l ≤ m ∧
      3 ≤ k * m ∧
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (k * m : ℕ) * (s : ℝ) ^ 2 * q := by sorry

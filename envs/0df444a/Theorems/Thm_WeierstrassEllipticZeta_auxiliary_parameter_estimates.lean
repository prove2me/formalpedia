-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_auxiliary_parameter_estimates
-- name    : WeierstrassEllipticZeta.auxiliary_parameter_estimates
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T15:02:47.46363+00:00
-- url     : https://prove2.me/theorems/4563b837-aea9-4d69-9506-b8e777a7c85d
-- title:
--   Rounded auxiliary parameters: dimension gap, zero count and interpolation radii
-- statement:
--   For a nonnegative integer $N$, define
--
--   $$m=\lfloor N/\log N\rfloor,\qquad
--   \ell=\lfloor\sqrt{N\log N}\rfloor,\qquad
--   s=\lfloor N^{3/16}\rfloor,\qquad
--   q=\lfloor N^{5/8}\log N/64\rfloor,\qquad
--   R=N^{49/72}.$$
--
--   Only sufficiently large $N$ enter the estimates. The formal definitions use nonnegative integer floors, which agree with the displayed floors there. The constant $1/64$ is one explicit small choice for the source's freely chosen grid constant.
--
--   Put
--
--   $$E=(m+1)s^2q,\qquad C=(m+1)(\ell+1)^2.$$
--
--   For every fixed real $A>0$, all sufficiently large integers $N$ satisfy
--
--   $$m,\ell,q\ge1,\qquad 2\le s\le q,\qquad 8E\le C,$$
--
--   $$\frac{N^2}{512}\le E\le\frac{N^2}{32},\qquad
--   m\log N\le N,\qquad \ell s^2\le m,$$
--
--   $$R\ge1,\qquad \frac{8Aq}{R}\le N^{-1/36},\qquad A\ell R^2\le N^2.$$
--
--   The threshold may depend on $A$. These inequalities supply the dimension gap for the auxiliary equations, a quadratic count of prescribed zeros, the basic arithmetic degree scale, and separation between the inner grid radius and the outer interpolation radius. They are explicit supporting bounds for the source's parameter choice and are not claimed to be verbatim numbered inequalities.
-- source:
--   Supporting estimates for Senthil Kumar K (2026), Section 5 parameter choice immediately before Lemma 7, the equation/unknown counts in the proof of Lemma 8, and equations (30)-(32). Explicit choice c21=1/64 and coarse constants 512, 32, 1/36 replace unspecified constants; these are not verbatim source inequalities. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryParameters

open Filter WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.auxiliary_parameter_estimates (A : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ auxiliaryL0 N ∧ 1 ≤ auxiliaryL N ∧ 2 ≤ auxiliaryS N ∧
      1 ≤ auxiliaryS3 N ∧ auxiliaryS N ≤ auxiliaryS3 N ∧
      8 * ((auxiliaryL0 N + 1) * auxiliaryS N ^ 2 * auxiliaryS3 N) ≤
        (auxiliaryL0 N + 1) * (auxiliaryL N + 1) ^ 2 ∧
      (N : ℝ) ^ 2 / 512 ≤
        (auxiliaryL0 N + 1 : ℝ) * auxiliaryS N ^ 2 * auxiliaryS3 N ∧
      (auxiliaryL0 N + 1 : ℝ) * auxiliaryS N ^ 2 * auxiliaryS3 N ≤
        (N : ℝ) ^ 2 / 32 ∧
      (auxiliaryL0 N : ℝ) * Real.log N ≤ N ∧
      auxiliaryL N * auxiliaryS N ^ 2 ≤ auxiliaryL0 N ∧
      1 ≤ auxiliaryRadius N ∧
      8 * A * auxiliaryS3 N / auxiliaryRadius N ≤ (N : ℝ) ^ (-1 / 36 : ℝ) ∧
      A * auxiliaryL N * auxiliaryRadius N ^ 2 ≤ (N : ℝ) ^ 2 := by sorry

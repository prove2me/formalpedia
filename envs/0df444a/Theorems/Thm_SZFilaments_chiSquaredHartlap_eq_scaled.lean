-- Prove2me | Theorems.Thm_SZFilaments_chiSquaredHartlap_eq_scaled
-- name    : SZFilaments.chiSquaredHartlap_eq_scaled
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:54:32.535485+00:00
-- url     : https://prove2.me/theorems/1232b5d2-d1a9-44ae-8e8c-0980321d78ac
-- title:
--   Eq. (7): the Hartlap correction rescales the chi-squared
-- statement:
--   **Equation (7) of the paper: the Hartlap correction rescales the chi-squared.**
--
--   The paper corrects the bias of the inverse of an estimated covariance by the factor of Hartlap, Simon & Schneider (2007), writing
--   $$\chi^2 = \sum_{i,j}\bar{y}_i\left[\frac{N_{\mathrm{sub}}-n-2}{N_{\mathrm{sub}}-1}\,C^{-1}\right]_{i,j}\bar{y}_j .$$
--   For every number of sub-samples $N_{\mathrm{sub}}$, every number of bins $n$, every matrix $C$ and every profile $\bar{y}$, this equals
--   $$\frac{N_{\mathrm{sub}}-n-2}{N_{\mathrm{sub}}-1}\sum_{i,j}\bar{y}_i (C^{-1})_{i,j}\bar{y}_j,$$
--   that is, the correction is a pure rescaling of the uncorrected statistic of Eq. (4) by the Hartlap factor. In particular the corrected statistic is nonnegative exactly when the factor and the uncorrected statistic have the same sign, which for $N_{\mathrm{sub}} > n+2$ and a positive definite $C$ means it is nonnegative.
-- source:
--   de Graaff A., Cai Y.-C., Heymans C., Peacock J. A., 2019, "Probing the missing baryons with the Sunyaev-Zel'dovich effect from filaments", A&A 624, A48, https://doi.org/10.1051/0004-6361/201935159, p. 5, Sect. 3.3, Eq. (7); correction factor from Hartlap, Simon & Schneider 2007, A&A 464, 399

import Definitions.Def_szStackStatistics
open Finset Matrix

namespace SZFilaments

theorem chiSquaredHartlap_eq_scaled {n : ℕ} (Nsub : ℕ) (C : Matrix (Fin n) (Fin n) ℝ)
    (ybar : Fin n → ℝ) :
    chiSquaredHartlap Nsub C ybar
      = (((Nsub : ℝ) - (n : ℝ) - 2) / ((Nsub : ℝ) - 1)) * chiSquared C ybar := by sorry

end SZFilaments

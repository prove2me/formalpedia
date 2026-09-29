-- Prove2me | Theorems.Thm_SZFilaments_jackknifeCovariance_posSemidef
-- name    : SZFilaments.jackknifeCovariance_posSemidef
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:49:10.289054+00:00
-- url     : https://prove2.me/theorems/ec1728ca-517c-40a0-a733-40b48a58b586
-- title:
--   Eqs. (5)-(6): the jackknife covariance is positive semidefinite
-- statement:
--   **Equations (5) and (6) of the paper: the jackknife covariance estimator is a covariance matrix.**
--
--   The paper replaces the naive covariance by a resampled one: the galaxy pairs are split into $N_{\mathrm{sub}}$ sky regions, each yielding a residual profile $y^k$, and
--   $$C^{JK}_{i,j} = \frac{N_{\mathrm{sub}}-1}{N_{\mathrm{sub}}}\sum_{k}(y^k_i-\bar{y}_i)(y^k_j-\bar{y}_j),\qquad \bar{y}_i = \frac{1}{N_{\mathrm{sub}}}\sum_k y^k_i .$$
--   This matrix is symmetric and positive semidefinite for every number of sub-samples and every data set: the jackknife prefactor $(N_{\mathrm{sub}}-1)/N_{\mathrm{sub}}$ is nonnegative, so it cannot spoil the positive semidefiniteness of the outer-product sum.
-- source:
--   de Graaff A., Cai Y.-C., Heymans C., Peacock J. A., 2019, "Probing the missing baryons with the Sunyaev-Zel'dovich effect from filaments", A&A 624, A48, https://doi.org/10.1051/0004-6361/201935159, pp. 4-5, Sect. 3.3, Eqs. (5) and (6)

import Definitions.Def_szStackStatistics
open Finset Matrix

namespace SZFilaments

theorem jackknifeCovariance_posSemidef {Nsub n : ℕ} (y : Fin Nsub → Fin n → ℝ) :
    (jackknifeCovariance y).PosSemidef := by sorry

end SZFilaments

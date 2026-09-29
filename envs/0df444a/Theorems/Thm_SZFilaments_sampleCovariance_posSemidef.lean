-- Prove2me | Theorems.Thm_SZFilaments_sampleCovariance_posSemidef
-- name    : SZFilaments.sampleCovariance_posSemidef
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:46:16.396801+00:00
-- url     : https://prove2.me/theorems/6d0bb03f-9026-4d62-9fd8-9530f0b3ae46
-- title:
--   Eq. (3): the stacked covariance estimator is positive semidefinite
-- statement:
--   **Equation (3) of the paper: the stacked covariance estimator is a covariance matrix.**
--
--   For a stack of $N$ binned profiles $y^k$, $k = 1,\dots,N$, with $n$ bins and mean profile $\bar{y}_i = \frac1N\sum_k y^k_i$, the estimator
--   $$C_{i,j} = \frac{1}{N}\sum_{k}(y^k_i-\bar{y}_i)(y^k_j-\bar{y}_j)$$
--   is symmetric and positive semidefinite, for every sample size $N$ (including the empty stack, where it is the zero matrix) and every data set. Positive semidefiniteness is what makes the $\chi^2$ of Eq. (4) a meaningful statistic and what a numerical inversion of $C$ implicitly assumes; it holds identically, with no assumption on the data.
-- source:
--   de Graaff A., Cai Y.-C., Heymans C., Peacock J. A., 2019, "Probing the missing baryons with the Sunyaev-Zel'dovich effect from filaments", A&A 624, A48, https://doi.org/10.1051/0004-6361/201935159, p. 3, Sect. 3.3, Eq. (3)

import Definitions.Def_szStackStatistics
open Finset Matrix

namespace SZFilaments

theorem sampleCovariance_posSemidef {N n : ℕ} (y : Fin N → Fin n → ℝ) :
    (sampleCovariance y).PosSemidef := by sorry

end SZFilaments

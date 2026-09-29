-- Prove2me | Theorems.Thm_SZFilaments_chiSquared_nonneg
-- name    : SZFilaments.chiSquared_nonneg
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:52:52.900361+00:00
-- url     : https://prove2.me/theorems/0d4e2c73-77d4-45f4-964d-976cabef33d0
-- title:
--   Eq. (4): the chi-squared statistic is nonnegative
-- statement:
--   **Equation (4) of the paper: the chi-squared statistic is nonnegative.**
--
--   For a mean profile $\bar{y}$ with $n$ bins and a covariance matrix $C$ that is positive definite, the statistic of Eq. (4),
--   $$\chi^2 = \sum_{i,j}\bar{y}_i\,(C^{-1})_{i,j}\,\bar{y}_j,$$
--   satisfies $\chi^2 \ge 0$. The hypothesis is positive definiteness of $C$ — not merely of $C^{-1}$ — which is the condition under which the inverse exists and is itself positive definite; without it the nonsingular inverse may be the zero matrix or indefinite and the quadratic form carries no sign.
-- source:
--   de Graaff A., Cai Y.-C., Heymans C., Peacock J. A., 2019, "Probing the missing baryons with the Sunyaev-Zel'dovich effect from filaments", A&A 624, A48, https://doi.org/10.1051/0004-6361/201935159, p. 3, Sect. 3.3, Eq. (4)

import Definitions.Def_szStackStatistics
open Finset Matrix

namespace SZFilaments

theorem chiSquared_nonneg {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (ybar : Fin n → ℝ) : 0 ≤ chiSquared C ybar := by sorry

end SZFilaments

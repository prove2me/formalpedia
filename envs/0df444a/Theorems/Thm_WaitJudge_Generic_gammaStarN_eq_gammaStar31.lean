-- Prove2me | Theorems.Thm_WaitJudge_Generic_gammaStarN_eq_gammaStar31
-- name    : WaitJudge.Generic.gammaStarN_eq_gammaStar31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:11:18.863545+00:00
-- url     : https://prove2.me/theorems/51825762-e3cf-4612-8166-3a447299464a
-- title:
--   (39), p. 27 — coefficient dual equals variational problem
-- statement:
--   Let γ*_N be the infimum of the coefficient dual (36) at M=N and let γ* be the infimum over feasible degree-at-most-N polynomials in (31). Then
--
--   $$
--   \gamma^*_N=\gamma^*.
--   $$
--
--   The equality identifies the coefficient dual bound with the variational quantity appearing in Theorem 3. Under the polynomial correspondence q(t)=∑_{m=0}^{N}λ_m t^m, evaluation at 1 gives ∑λ_m, while q^{(k)}(t)/k! gives the dual polynomial for index k.
--
--   **Formalization Note** Both sides are real infima of explicitly defined feasible-value sets. The identity is algebraic and has no probabilistic hypotheses. The reading of P_N as degree at most N matches the N+1 free coefficients.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF p. 27, (39), with coefficient formula displayed immediately above

import Mathlib
import Definitions.Def_WaitJudge_Generic_Setting

namespace WaitJudge.Generic

open MeasureTheory

theorem gammaStarN_eq_gammaStar31
    (N : ℕ) (ε : ℕ → ℝ) :
    gammaStarDualN N ε = gammaStar31 N ε := by sorry

end WaitJudge.Generic

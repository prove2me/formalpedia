-- Prove2me | Theorems.Thm_PSOutsourcing_PartialObs_condLoss_limit
-- name    : PSOutsourcing.PartialObs.condLoss_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:00.32365+00:00
-- url     : https://prove2.me/theorems/81a3a8bd-c6f7-4a18-9cc3-0ac77cb57a82
-- title:
--   Proof of Proposition 4(c), p. A-7 — the conditional expected loss tends to αCβk̄d^b_i as s_i → ∞
-- statement:
--   Let the model parameters satisfy the standing assumptions. As the variance parameter $s$ of the information gap tends to infinity,
--   $$
--   \lim_{s\to\infty}\mathbb E\big[c^S(\bar k,d^b)-c^S(\bar k,d)\,\big|\,d\le d^b\big]=\alpha C\beta\bar k d^b ,
--   $$
--   with $d=\xi_s d^b$, $\xi_s=\exp(sZ-s^2/2)$, $Z\sim N(0,1)$, and the conditional expectation as in the closed-form milestone.
--
--   In the proof of Proposition 4(c) this limit is what makes the loss eventually exceed any fixed gain from outsourcing.
-- source:
--   Wang, Li, Ma & Zhang, Product service outsourcing: impact of environment uncertainty and partial observability, accepted manuscript (MSOM 2024, doi:10.1287/msom.2022.0222), p. A-7 (PDF 39), proof of Proposition 4(c), 'As s_i increases (visibility worsens), …'

import Mathlib
import Definitions.Def_PSOutsourcing_PartialObs_Model

open MeasureTheory ProbabilityTheory

namespace PSOutsourcing.PartialObs

theorem condLoss_limit (P : Params) (hP : P.Standing) :
    Filter.Tendsto (condLoss P) Filter.atTop (nhds (P.α * P.C * P.β * P.kbar * P.db)) := by sorry

end PSOutsourcing.PartialObs

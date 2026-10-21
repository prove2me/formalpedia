-- Prove2me | Theorems.Thm_PSOutsourcing_PartialObs_expected_payment
-- name    : PSOutsourcing.PartialObs.expected_payment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:02.159037+00:00
-- url     : https://prove2.me/theorems/ab2d7daf-bf26-425e-8398-9ddafe0e7574
-- title:
--   Proof of Proposition 4(a), p. A-7 — E[c^S(k̄, d̃_i)] = c^S(k̄, d^b_i)
-- statement:
--   Let the model parameters satisfy the standing assumptions and let $s\in\mathbb R$. With the random true environment $\tilde d=\xi_s d^b$, $\xi_s=\exp(sZ-s^2/2)$, $Z\sim N(0,1)$,
--   $$
--   \mathbb E\big[c^S(\bar k,\tilde d)\big]=c^S(\bar k,d^b),\qquad c^S(k,d)=\alpha C k(1+\beta d).
--   $$
--
--   In the proof of Proposition 4(a) this identity shows that paying the provider at the point estimate $d^b$ is consistent with the brand accounting for the uncertainty in the environment.
-- source:
--   Wang, Li, Ma & Zhang, Product service outsourcing: impact of environment uncertainty and partial observability, accepted manuscript (MSOM 2024, doi:10.1287/msom.2022.0222), p. A-7 (PDF 39), proof of Proposition 4(a), 'Then for any given k̄ the expected service provision cost is given by …'

import Mathlib
import Definitions.Def_PSOutsourcing_PartialObs_Model

open MeasureTheory ProbabilityTheory

namespace PSOutsourcing.PartialObs

theorem expected_payment (P : Params) (hP : P.Standing) (s : ℝ) :
    ∫ z, costS P P.kbar (xi s z * P.db) ∂(gaussianReal 0 1) = costS P P.kbar P.db := by sorry

end PSOutsourcing.PartialObs

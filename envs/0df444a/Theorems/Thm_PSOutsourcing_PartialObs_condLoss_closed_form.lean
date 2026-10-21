-- Prove2me | Theorems.Thm_PSOutsourcing_PartialObs_condLoss_closed_form
-- name    : PSOutsourcing.PartialObs.condLoss_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:01.066681+00:00
-- url     : https://prove2.me/theorems/00606a4d-7057-4abf-ad1f-48053776f1c3
-- title:
--   Proof of Proposition 4(c), p. A-7 — E[c^S(k̄,d^b_i) − c^S(k̄,d_i) | d_i ≤ d^b_i] = αCβk̄d^b_i(1 − (1 − erf(s_i/2√2))/(1 − erf(−s_i/2√2)))
-- statement:
--   Let the model parameters satisfy the standing assumptions and let $s>0$. With $d=\xi_s d^b$, $\xi_s=\exp(sZ-s^2/2)$, $Z\sim N(0,1)$, the expected overpayment of the brand, conditional on its belief lying above the true environment, is
--   $$
--   \mathbb E\big[c^S(\bar k,d^b)-c^S(\bar k,d)\,\big|\,d\le d^b\big]
--   =\alpha C\beta\bar k d^b\left(1-\frac{1-\operatorname{erf}\big(s/(2\sqrt2)\big)}{1-\operatorname{erf}\big(-s/(2\sqrt2)\big)}\right).
--   $$
--   Here the conditional expectation is $\frac{1}{\mathbb P(\xi_s\le 1)}\int_{\{\xi_s\le1\}}(\cdot)\,d\mathbb P$, and $\operatorname{erf}$ is the error function.
--
--   In the proof of Proposition 4(c) this closed form quantifies the expected value loss from the belief drifting above the actual environment.
--
--   **Formalization Note** The page's first display writes the integral $\int_{\xi\le 1}$ without the normalisation $1/F_i(1)$ that its second display has; the normalised (conditional) form is the one stated. The event $\{\xi_s\le 1\}=\{Z\le s/2\}$ has positive probability, so the division is never by $0$.
-- source:
--   Wang, Li, Ma & Zhang, Product service outsourcing: impact of environment uncertainty and partial observability, accepted manuscript (MSOM 2024, doi:10.1287/msom.2022.0222), p. A-7 (PDF 39), proof of Proposition 4(c), the two displays after 'Part (c).'

import Mathlib
import Definitions.Def_PSOutsourcing_PartialObs_Model

open MeasureTheory ProbabilityTheory

namespace PSOutsourcing.PartialObs

theorem condLoss_closed_form (P : Params) (hP : P.Standing) (s : ℝ) (hs : 0 < s) :
    condLoss P s = P.α * P.C * P.β * P.kbar * P.db *
      (1 - (1 - erf (s / (2 * Real.sqrt 2))) / (1 - erf (-s / (2 * Real.sqrt 2)))) := by sorry

end PSOutsourcing.PartialObs

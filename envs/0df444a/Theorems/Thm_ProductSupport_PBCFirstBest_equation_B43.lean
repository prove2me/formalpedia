-- Prove2me | Theorems.Thm_ProductSupport_PBCFirstBest_equation_B43
-- name    : ProductSupport.PBCFirstBest.equation_B43
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:38.723128+00:00
-- url     : https://prove2.me/theorems/8f46f908-caef-4a5b-b41b-1afdb0460c04
-- title:
--   (B.43) — IC conditions and the reservation-payoff ratio interval
-- statement:
--   For positive repair rates above the high failure rate, substitute the two prices that bind the corresponding IR constraints. Both types prefer their designated contracts exactly when
--   $$
--   \frac{\mu_H-\lambda_L}{\mu_H-\lambda_H}
--   \leq\frac{M_L}{M_H}
--   \leq\frac{\mu_L-\lambda_L}{\mu_L-\lambda_H}.
--   $$
--   This is condition (B.43), the comparison that becomes condition (10) at the first-best rates.
--
--   **Formalization Note** The source states that the two IC constraints imply this interval. The Lean statement also records the converse needed for Proposition 5(i); the two directions are equivalent under the displayed positive-denominator regime. The assumptions $\mu_L,\mu_H>\lambda_H$ rule out the zero and sign-reversing denominator cases.
-- source:
--   Li, Mishra & Netessine, Contracting for Product Support under Information Asymmetry, SSRN 2881356 (author version of Management Science, doi:10.1287/mnsc.2022.4606), supplement p. 9 (PDF 42), proof of Proposition 5(i), (B.43)

import Mathlib
import Definitions.Def_ProductSupport_PBCFirstBest_Model

namespace ProductSupport.PBCFirstBest

theorem equation_B43 (P : Params) (hS : P.Standing) (muL muH : ℝ)
    (hmuL : P.lamH < muL) (hmuH : P.lamH < muH) :
    (custPayoff P P.lamL ⟨vBinding P P.lamL P.ML muL, muL⟩ -
        custPayoff P P.lamL ⟨vBinding P P.lamH P.MH muH, muH⟩ ≥ 0 ∧
      custPayoff P P.lamH ⟨vBinding P P.lamH P.MH muH, muH⟩ -
        custPayoff P P.lamH ⟨vBinding P P.lamL P.ML muL, muL⟩ ≥ 0) ↔
      (muH - P.lamL) / (muH - P.lamH) ≤ P.ML / P.MH ∧
      P.ML / P.MH ≤ (muL - P.lamL) / (muL - P.lamH) := by sorry

end ProductSupport.PBCFirstBest

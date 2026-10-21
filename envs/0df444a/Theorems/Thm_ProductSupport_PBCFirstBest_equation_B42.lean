-- Prove2me | Theorems.Thm_ProductSupport_PBCFirstBest_equation_B42
-- name    : ProductSupport.PBCFirstBest.equation_B42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:41.853821+00:00
-- url     : https://prove2.me/theorems/e32d523b-952f-4362-bc56-f1a0820abd58
-- title:
--   (B.42) — high-type incentive-compatibility slack at binding-IR prices
-- statement:
--   Let $\mu_L,\mu_H>0$ be repair rates distinct from their respective failure rates, and substitute the two binding-IR prices $v_\tau=r+M_\tau\mu_\tau/(\lambda_\tau-\mu_\tau)$. The high type's incentive-compatibility slack is
--   $$
--   \pi_{cH}^P(v_H,\mu_H)-\pi_{cH}^P(v_L,\mu_L)
--   =M_H+\frac{M_L(-\lambda_H+\mu_L)}{\lambda_L-\mu_L}.
--   $$
--   The identity is the paper's calculation (B.42). Its sign determines whether the high type prefers the designated contract.
--
--   **Formalization Note** Nonzero denominators are stated explicitly. The equation itself does not claim that the slack is nonnegative for every repair-rate pair.
-- source:
--   Li, Mishra & Netessine, Contracting for Product Support under Information Asymmetry, SSRN 2881356 (author version of Management Science, doi:10.1287/mnsc.2022.4606), supplement p. 9 (PDF 42), proof of Proposition 5(i), (B.42)

import Mathlib
import Definitions.Def_ProductSupport_PBCFirstBest_Model

namespace ProductSupport.PBCFirstBest

theorem equation_B42 (P : Params) (hS : P.Standing) (muL muH : ℝ)
    (hmuL : 0 < muL) (hmuH : 0 < muH)
    (hneL : muL ≠ P.lamL) (hneH : muH ≠ P.lamH) :
    (custPayoff P P.lamH ⟨vBinding P P.lamH P.MH muH, muH⟩ -
      custPayoff P P.lamH ⟨vBinding P P.lamL P.ML muL, muL⟩ =
      P.MH + P.ML * (-P.lamH + muL) / (P.lamL - muL)) ∧
    (custPayoff P P.lamH ⟨vBinding P P.lamL P.ML muL, muL⟩ ≤
      custPayoff P P.lamH ⟨vBinding P P.lamH P.MH muH, muH⟩ ↔ 0 ≤ P.MH + P.ML * (-P.lamH + muL) / (P.lamL - muL)) := by sorry

end ProductSupport.PBCFirstBest

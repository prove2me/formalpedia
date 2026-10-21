-- Prove2me | Theorems.Thm_ProductSupport_PBCFirstBest_equation_B41
-- name    : ProductSupport.PBCFirstBest.equation_B41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:33.333212+00:00
-- url     : https://prove2.me/theorems/36b0ee3b-8064-4888-a925-8b7d3b58d153
-- title:
--   (B.41) — low-type incentive-compatibility slack at binding-IR prices
-- statement:
--   Let $\mu_L,\mu_H>0$ be repair rates distinct from their respective failure rates, and substitute the two binding-IR prices $v_\tau=r+M_\tau\mu_\tau/(\lambda_\tau-\mu_\tau)$. The low type's incentive-compatibility slack is
--   $$
--   \pi_{cL}^P(v_L,\mu_L)-\pi_{cL}^P(v_H,\mu_H)
--   =M_L+\frac{M_H(-\lambda_L+\mu_H)}{\lambda_H-\mu_H}.
--   $$
--   The identity is the paper's calculation (B.41). Its sign determines whether the low type prefers the designated contract.
--
--   **Formalization Note** Nonzero denominators are stated explicitly. The equation itself does not claim that the slack is nonnegative for every repair-rate pair.
-- source:
--   Li, Mishra & Netessine, Contracting for Product Support under Information Asymmetry, SSRN 2881356 (author version of Management Science, doi:10.1287/mnsc.2022.4606), supplement p. 9 (PDF 42), proof of Proposition 5(i), (B.41)

import Mathlib
import Definitions.Def_ProductSupport_PBCFirstBest_Model

namespace ProductSupport.PBCFirstBest

theorem equation_B41 (P : Params) (hS : P.Standing) (muL muH : ℝ)
    (hmuL : 0 < muL) (hmuH : 0 < muH)
    (hneL : muL ≠ P.lamL) (hneH : muH ≠ P.lamH) :
    (custPayoff P P.lamL ⟨vBinding P P.lamL P.ML muL, muL⟩ -
      custPayoff P P.lamL ⟨vBinding P P.lamH P.MH muH, muH⟩ =
      P.ML + P.MH * (-P.lamL + muH) / (P.lamH - muH)) ∧
    (custPayoff P P.lamL ⟨vBinding P P.lamH P.MH muH, muH⟩ ≤
      custPayoff P P.lamL ⟨vBinding P P.lamL P.ML muL, muL⟩ ↔ 0 ≤ P.ML + P.MH * (-P.lamL + muH) / (P.lamH - muH)) := by sorry

end ProductSupport.PBCFirstBest

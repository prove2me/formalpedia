-- Prove2me | Theorems.Thm_SolarNonOwn_BizChoice_compare_thresholds
-- name    : SolarNonOwn.BizChoice.compare_thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:06.557988+00:00
-- url     : https://prove2.me/theorems/a683f79c-b388-4208-a454-1c5457dcde6a
-- title:
--   Comparing A and B, p. OA7 — subsidy thresholds A₁ < A₂ < A
-- statement:
--   With positive generation subsidy $\beta$, positive transaction cost $t<r$, and $\beta<r$, the proof's subsidy thresholds satisfy
--
--   $$A_1=\frac{\beta t}{r(r+\beta)+\beta t}<A_2=\frac{\beta}{\beta+r}<A=\sqrt{\frac{\beta(r+t)}{r(r+\beta)+\beta t}}.$$
--
--   The ordering separates the three subsidy cases used to compare the A and B regional optima.
-- source:
--   Agrawal, Toktay & Yücel, Non-Ownership Business Models for Solar Energy, authors' manuscript of 18 Sep 2021 (MSOM, doi:10.1287/msom.2021.1049), p. OA7 (PDF p. 39), proof of Proposition 1, Comparing A and B

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_ClosedForms

namespace SolarNonOwn.BizChoice

/-- Comparing A and B, p. OA7: A1 < A2 < A. -/
theorem compare_thresholds (prm : Params) (hβ : 0 < prm.beta)
    (ht : 0 < prm.t) (htr : prm.t < prm.r) (hβr : prm.beta < prm.r) :
    A1 prm < A2 prm ∧ A2 prm < Acon prm := by sorry

end SolarNonOwn.BizChoice

-- Prove2me | Theorems.Thm_SellVsPPU_Duopoly_a21_ppu_best_response
-- name    : SellVsPPU.Duopoly.a21_ppu_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:12.746086+00:00
-- url     : https://prove2.me/theorems/33b91f65-bd3e-4f71-88b6-ec82a794f5d6
-- title:
--   A.2.1, p. 36 — service best response, globally (stronger than printed)
-- statement:
--   Let $a>0$ be value per use, $q_m>0$ the maximum usage, $c>0$ the product cost, and $\delta\ge0$ the delivery cost per use. Assume the service cost $c_u=c/q_m+\delta$ does not exceed $a$.
--
--   Fix a seller price $0<p_s\le q_m\min(2c_u,a)$. The service provider maximizes its profit among all prices $p_u'\le a$ by charging $\min(2c_u,a)$:
--
--   $$
--   \Pi_u(p_s,p_u')\le\Pi_u\bigl(p_s,\min(2c_u,a)\bigr)
--   \quad\text{for every }p_u'\le a.
--   $$
--
--   The candidate equals twice cost when that price is feasible, and equals the value cap otherwise.
--
--   **Formalization Note** The printed KKT calculation is local to the interior profit formula. The theorem also covers deviations where the provider serves the entire market or charges a nonpositive price.
-- source:
--   Ladas, Kavadias & Loch, Product Selling vs. Pay-Per-Use Service, SSRN 3356458 manuscript (PDF of 16 Apr 2021; Management Science, doi:10.1287/mnsc.2021.4125), p. 36, A.2.1, service-provider KKT paragraph

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model

namespace SellVsPPU.Duopoly

/-- Stronger than printed: the paper checks KKT candidates in the interior formula; this theorem asserts global optimality over every service price at most a. -/
theorem a21_ppu_best_response (P : Params) (hP : P.Admissible)
    (ps : ℝ) (hps : 0 < ps) (hpsq : ps ≤ P.qm * min (2 * cu P) P.a) :
    min (2 * cu P) P.a ≤ P.a ∧
    ∀ pu' : ℝ, pu' ≤ P.a →
      profitU P ps pu' ≤ profitU P ps (min (2 * cu P) P.a) := by sorry

end SellVsPPU.Duopoly

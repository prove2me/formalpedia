-- Prove2me | Theorems.Thm_TokenSignal_Asymmetry_proposition_5
-- name    : TokenSignal.Asymmetry.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:52.305143+00:00
-- url     : https://prove2.me/theorems/decd1b75-b191-4177-9918-a9bf6ffa3e5f
-- title:
--   Proposition 5: unique least-cost separating equilibrium
-- statement:
--   For either equity or token financing, if the high type can meet its financing threshold at $\alpha^*$, that is, $\bar\alpha_H^i\le\alpha^*$, there is a unique least-cost separating equilibrium. Its belief threshold is $t^i=\alpha^*$; the high type uniquely chooses $\alpha_H^i=\alpha^*$ and the low type uniquely chooses $\alpha_L^i=1$. If instead $\alpha^*<\bar\alpha_H^i$, no separating equilibrium exists.
--
--   Thus the financing threshold determines whether each security can support separation.
-- source:
--   Chod & Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (version of Dec. 14, 2019), p. 20 (PDF 21), Proposition 5

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_Model

namespace TokenSignal.Asymmetry

theorem proposition_5 (P : Params) (hS : P.Standing) (m : Method) :
    (αbar P m .H ≤ αStar P →
      (∀ t, IsLCSE P m t ↔ t = αStar P) ∧
      (αStar P ∈ Hset P m (αStar P) ∧
        ∀ α ∈ Hset P m (αStar P), α ≠ αStar P →
          U P .H .H α < U P .H .H (αStar P)) ∧
      ((1 : ℝ) ∈ Lset P m (αStar P) ∧
        ∀ α ∈ Lset P m (αStar P), α ≠ 1 →
          U P .L .L α < U P .L .L 1)) ∧
    (αStar P < αbar P m .H → ¬ ∃ t, IsSE P m t) := by sorry
end TokenSignal.Asymmetry

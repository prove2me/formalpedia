-- Prove2me | Theorems.Thm_PlatformEntry_Regimes_lemma2_optimal_effort
-- name    : PlatformEntry.Regimes.lemma2_optimal_effort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:39.504589+00:00
-- url     : https://prove2.me/theorems/24fcf32e-baf8-4bb3-8f52-071e9680f027
-- title:
--   Lemma 2, PDF p. 12 — under (5), the platform's optimal effort e*_P and the seller stays (q*_S > 0)
-- statement:
--   Let $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$ satisfy condition (5), let $a + e_S > 0$, and let $K$ be any entry cost. Consider the platform's stage-2 problem after entry: it chooses an effort $e_P \ge 0$, anticipating that any effort is followed by an equilibrium of the quantity game. Then:
--
--   1. $(e_P, q_S, q_P)$ is an entry equilibrium (the effort is optimal against every effort $e_P' \ge 0$ followed by any quantity equilibrium, and $(q_S,q_P)$ is a quantity equilibrium given $e_P$) if and only if $(q_S,q_P)$ is a quantity equilibrium given $e_P$ and
--   $$
--   e^*_P = \frac{(a+e_S)\big(8 + 8\delta f - 4\beta(1+\delta)(1+f) + \beta^3(1+\delta)f(1+f) - 2\beta^2(f+\delta(-1+f^2))\big)}{8 - 8\delta^2 f + 8\beta\delta(1+f) - 2\beta^3\delta f(1+f) + \beta^4(1+f)^2 + 2\beta^2(-4-3f+\delta^2(-1+f^2))};
--   $$
--   2. in every entry equilibrium the seller remains in the market: $q^*_S > 0$.
--
--   Only the branch of Lemma 2 under condition (5) is formalized: (5) is the paper's standing assumption from this point on (p. 12), and the opt-out branch $e^*_P = (2-\beta)(a+e_S)/(\beta - 2\delta)$, $q^*_S = 0$ is not used by the goal.
--
--   **Formalization Note** "Optimal" means a global maximizer over $e_P \ge 0$, ties allowed. The platform's effort is restricted to $e_P \ge 0$ (effort is nonnegative). $a + e_S > 0$ is the economic setting of a positive product value.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), PDF p. 12, Lemma 2 (branch under (5)); proof Online Supplement, Appendix A, PDF p. 32

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model

namespace PlatformEntry.Regimes

theorem lemma2_optimal_effort (δ f β K a eS : ℝ) (hbox : InBox δ f β) (h5 : cond5 δ f β)
    (hA : 0 < a + eS) :
    (∀ eP qS qP : ℝ, IsEntryEq δ f β K (a + eS) eP qS qP ↔
        (eP = (a + eS) * ePNum δ f β / D δ f β ∧ IsQuantityEq δ f β K (a + eS) eP qS qP)) ∧
    (∀ eP qS qP : ℝ, IsEntryEq δ f β K (a + eS) eP qS qP → 0 < qS) := by sorry

end PlatformEntry.Regimes

-- Prove2me | Theorems.Thm_WeldedPath_Supplement_exact_query_goodness
-- name    : WeldedPath.Supplement.exact_query_goodness
-- status  : Open
-- author  : @dmilosch
-- created : 2026-11-22T16:09:18.468226+00:00
-- url     : https://prove2.me/theorems/861e4329-2191-492f-8c1a-c19f3957dd4a
-- title:
--   Good-space leakage of one exact compressed welded-tree query
-- statement:
--   Let N=2^n, N_l=2^(n-l), and epsilon_l=2^(-l). There are absolute constants C0,C>0 such that, for every even n>=16, 2<=l<=n-4, valid properly colored welded-tree instance G, and integers q,t>=0 with t<=6q, the two small-query conditions C0(q+1)<=N_l and C0((q+1)epsilon_l+(n+1)(q+1)^3/N)<=1/2 imply
--     ||(Id-P_good_(t+6)) exactCpWT P_good_t|| <= C sqrt(epsilon_l+n(t+1)/N).
--   The norm is the operator norm on the canonical query-register/database Hilbert space. Both constants precede all graph and budget parameters. This is a local, single-query estimate and does not quantify over algorithms or workspaces. The source writes an equivalent bound using sqrt(epsilon_l)+sqrt(n(t+1)/N); the absolute constant absorbs the factor at most sqrt(2).
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1#S4.SS3, Proposition 4.12 and the small-query assumptions (49). This is the exact-query goodness estimate used in Section 4.5 to derive equation (78). The ordinary-query analogue is Theorem 4.9; the localized ordinary-to-exact argument is essential.

import Mathlib
import Definitions.Def_WeldedPath_Supplement_projGood
import Definitions.Def_WeldedPath_Supplement_exactCpWT

set_option autoImplicit false

namespace WeldedPath

namespace Supplement

theorem exact_query_goodness :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ q t : ℕ, t ≤ 6 * q →
      C₀ * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      C₀ * (((q : ℝ) + 1) / (2 : ℝ) ^ l +
        ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤ 1 / 2 →
      ‖(1 - projGood l G (t + 6)).comp
          ((exactCpWT l G).comp (projGood l G t))‖ ≤
        C * etaStep n l t := by sorry

end Supplement

end WeldedPath

-- Prove2me | Theorems.Thm_VectorPayoffs_Convex_T_approachable_transpose
-- name    : VectorPayoffs.Convex.T_approachable_transpose
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:10:35.676153+00:00
-- url     : https://prove2.me/theorems/6ac42baa-5371-43ca-b4fc-95b733bc7981
-- title:
--   Proof of THEOREM 3, second paragraph — every T(q₀) is approachable in M′ with fₙ ≡ q₀
-- statement:
--   For every $q_0\in Q$, the set $T(q_0)$ is approachable in the transpose game $M'$ with the stationary strategy $f_n\equiv q_0$.
--
--   In $M'$ the roles are exchanged: the set $R'(q_0)$ of $M'$ equals $T(q_0)$, so $T(q_0)$ satisfies THEOREM 1's hypothesis in $M'$ with $p(x)\equiv q_0$. With the transpose fact this yields the excludability clause of THEOREM 3.
--
--   **Formalization Note** The paper states the sentence "any $T(q_0)$ satisfies the hypotheses of Theorem 1 in $M'$ with $f: f_n\equiv q_0$, and so is approachable in $M'$ with this $f$"; the item formalizes its conclusion.
-- source:
--   Blackwell, An analog of the minimax theorem for vector payoffs, Pacific J. Math. 6(1), 1956, p. 6, §3, proof of THEOREM 3, second paragraph, first sentence

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §3, proof of THEOREM 3, p. 6, second paragraph: every `T(q₀)` is
approachable in the transpose `M'` with the stationary strategy `fₙ ≡ q₀`. -/
theorem T_approachable_transpose {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)) :
    G.transpose.ApproachableWith (G.T q₀) (Strategy.const q₀ hq₀) := by sorry

end VectorPayoffs.Convex

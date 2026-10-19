-- Prove2me | Theorems.Thm_PBElicit_RandThresh_final_mechanism
-- name    : PBElicit.RandThresh.final_mechanism
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:34.389378+00:00
-- url     : https://prove2.me/theorems/5dbc0e4b-90e6-4905-a177-b32d07c20209
-- title:
--   Proof of Theorem 3.5, p. 14 — for m a power of 2, some randomized threshold rule has distortion at most 2 + 16 log² m
-- statement:
--   Let $m=2^K$ be the number of alternatives, with costs $c_a\in[0,1]$ and budget $1$, and let there be $n$ voters. There is a randomized threshold rule $R$, fixed before the utilities are known and seeing only threshold approval votes, such that for every normalized utility profile $\vec v$ and every $T\in\mathcal F_c$,
--   $$
--   \mathrm{sw}(T,\vec v)\ \le\ \big(2+16\log^2 m\big)\cdot\mathbb E[\mathrm{sw}(R,\vec v)].
--   $$
--   The page's rule runs Mechanism A with probability $16\log^2 m/(2+16\log^2 m)$ and Mechanisms B and C (fund the cheapest bucket; pick one alternative uniformly) with probability $1/(2+16\log^2 m)$ each.
--
--   This is the explicit-constant form of Theorem 3.5 for $m$ a power of $2$.
--
--   **Formalization Note.** $\log$ is $\log_2$. $\mathbb E[\mathrm{sw}]$ is the expectation over the threshold and the aggregation together (see the goal's note). Rule outputs lie in $\mathcal F_c$, so the mechanisms' feasible outputs are extended to inclusion-maximal feasible sets. Costs in $[0,1]$ are a disclosed reading (Mechanism C needs each single alternative to be feasible).
-- source:
--   Benadè, Nath, Procaccia & Shah, Preference Elicitation for Participatory Budgeting, author's manuscript (2018; Manag. Sci. 2021, doi:10.1287/mnsc.2020.3666), proof of Theorem 3.5, Mechanism C and final mechanism, p. 14

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

namespace PBElicit.RandThresh

theorem final_mechanism {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (hc : ∀ a, 0 ≤ c a ∧ c a ≤ 1) (m K : ℕ) (hA : Fintype.card A = m) (hmK : m = 2 ^ K) :
    ∃ R : ThresholdRule n A c, ∀ v : Fin n → A → ℝ, IsUtilityProfile v →
      ∀ T : Finset A, IsMaxFeasible c T →
        sw v T ≤ (2 + 16 * Real.logb 2 m ^ 2) * R.expWelfare v := by sorry

end PBElicit.RandThresh

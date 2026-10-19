-- Prove2me | Theorems.Thm_PBElicit_RandThresh_observation_3_1
-- name    : PBElicit.RandThresh.observation_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:55.472187+00:00
-- url     : https://prove2.me/theorems/16205f4a-eb66-4ad9-a666-e321f518662b
-- title:
--   Observation 3.1, p. 7 — the uniform single-alternative rule has distortion at most m
-- statement:
--   Let $A$ be a set of $m\ge 1$ alternatives with costs $c_a\in[0,1]$, budget $1$, and $n$ voters. There is a randomized threshold rule $R$ (fixed before the utilities are known) whose aggregation maps ignore the votes, such that for every normalized utility profile $\vec v$ and every $T\in\mathcal F_c$,
--   $$
--   \mathrm{sw}(T,\vec v)\ \le\ m\cdot\mathbb E[\mathrm{sw}(R,\vec v)].
--   $$
--   In words: the distortion of some rule is at most $m$. The page's rule selects a single alternative uniformly at random and ignores the votes.
--
--   This is the baseline that Theorem 3.5 improves to $O(\log^2 m)$; it is also Mechanism C of that proof.
--
--   **Formalization Note.** The page states the bound for "any input format". The statement asserts a rule that "does not require any input": every arm's aggregation map is constant in the approval profile, so the same distribution over $\mathcal F_c$ is a rule for every input format, and the bound holds for all of them; the threshold-approval type is only the carrier. Rules must output sets of $\mathcal F_c$, so a single alternative is extended to an inclusion-maximal feasible set. Costs in $[0,1]$ are a disclosed reading: the page uses that each single alternative is budget-feasible. The distortion is stated multiplicatively, $\mathrm{OPT}\le m\cdot\mathbb E[\mathrm{sw}]$.
-- source:
--   Benadè, Nath, Procaccia & Shah, Preference Elicitation for Participatory Budgeting, author's manuscript (2018; Manag. Sci. 2021, doi:10.1287/mnsc.2020.3666), Observation 3.1, p. 7

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

namespace PBElicit.RandThresh

theorem observation_3_1 {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (hc : ∀ a, 0 ≤ c a ∧ c a ≤ 1) (hm : 1 ≤ Fintype.card A) :
    ∃ R : ThresholdRule n A c, (∀ r ρ ρ', R.agg r ρ = R.agg r ρ') ∧
      ∀ v : Fin n → A → ℝ, IsUtilityProfile v →
        ∀ T : Finset A, IsMaxFeasible c T →
          sw v T ≤ (Fintype.card A : ℝ) * R.expWelfare v := by sorry

end PBElicit.RandThresh

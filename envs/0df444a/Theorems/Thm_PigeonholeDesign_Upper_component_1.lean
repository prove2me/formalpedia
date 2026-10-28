-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_component_1
-- name    : PigeonholeDesign.Upper.component_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:58.049803+00:00
-- url     : https://prove2.me/theorems/b8d36055-5dd0-4fc4-a93c-8717799d2e7e
-- title:
--   Proof of Lemma 3, Component 1, p. ec8 — the matched subjects contribute O(T^{1/2−η/2})
-- statement:
--   There is an absolute constant $C>0$ with the following property. For every $\eta\in(0,1)$, every even $T\ge1$ and every arrival sequence $x\in[0,1]^T$, run the pigeonhole design with the $\lceil T^{\eta}\rceil$ uniform pigeonholes of $[0,1]$, and let $\mathcal T_M$ be the (coin-dependent) set of matched subjects. Then the expected discrepancy between the control and the treated subjects of $\mathcal T_M$ satisfies
--   $$\mathbb E\bigl[d_{A\cap\mathcal T_M,\ B\cap\mathcal T_M}\bigr]\ \le\ C\,T^{\frac12-\frac\eta2}.$$
--
--   This is the first of the two components of the proof of Lemma 3: subjects paired inside a short pigeonhole are cheap to match.
--
--   **Formalization Note** The expectation is the average over all $2^T$ coin vectors of the minimum-weight perfect matching between the matched control and matched treated subjects; these two sets have equal size on every run (see the milestone on unmatched subjects), so the junk value of an unbalanced matching is never used. $C$ is chosen before $\eta$, $T$ and $x$, as the page's "absolute constant".
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec8 (PDF p. 46), proof of Lemma 3, Component 1

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting
import Definitions.Def_PigeonholeDesign_Upper_Stopping

namespace PigeonholeDesign.Upper

theorem component_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η < 1 → ∀ T : ℕ, 1 ≤ T → Even T →
      ∀ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) →
        (∑ coin : Fin T → Bool,
            discrepancyOn x (assign (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin)
              (matched (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin)) / 2 ^ T
          ≤ C * (T : ℝ) ^ (1 / 2 - η / 2) := by sorry

end PigeonholeDesign.Upper

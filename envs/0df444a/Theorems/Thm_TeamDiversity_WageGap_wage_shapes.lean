-- Prove2me | Theorems.Thm_TeamDiversity_WageGap_wage_shapes
-- name    : TeamDiversity.WageGap.wage_shapes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:29.365822+00:00
-- url     : https://prove2.me/theorems/16a6d9cd-8b71-42ba-bdd4-7a590bffe895
-- title:
--   §3, p. 20 — E[w_d*] strictly decreases in δ on [0,1]; E[w_s**] strictly decreases on [0, δ^C] and strictly increases on [δ^C, 1]
-- statement:
--   Under the standing assumptions, let $w_s^{**}(\delta)$ and $w_d^*(\delta)$ be, for each $\delta \in [0,1]$, the least feasible wages of the specialized program (with No-cycling) and of the diverse program. Then
--
--   1. the diverse expected wage $\delta \mapsto E[w_d^*] = f_d(2)\,w_d^*(\delta)$ is strictly decreasing on $[0,1]$;
--   2. the specialized expected wage $\delta \mapsto E[w_s^{**}] = f_s(2)\,w_s^{**}(\delta)$ is strictly decreasing on $[0,\delta^C]$;
--   3. it is strictly increasing on $[\delta^C, 1]$.
--
--   So the mutual-monitoring wage falls with patience while the collusion-proof wage rises once collusion binds.
--
--   **Formalization Note** The optimal wages enter as arbitrary functions characterized only by being least elements of the feasible sets on $[0,1]$.
-- source:
--   Glover & Kim, Optimal Team Composition: Diversity to Foster Implicit Team Incentives, SSRN working paper 3344922 (June 2020 version), §3, p. 20 (PDF 21) (summary paragraph), with p. 16 (PDF 17)

import Mathlib
import Definitions.Def_TeamDiversity_WageGap_Model

namespace TeamDiversity.WageGap

/-- §3, p. 20 (with p. 16): the diverse mutual-monitoring expected wage strictly decreases on
`[0,1]`; the specialized collusion-proof expected wage strictly decreases on `[0, δ^C]` and strictly
increases on `[δ^C, 1]`. -/
theorem wage_shapes (c : ℝ) (fs fd : Tech) (hst : Standing c fs fd) (ws wd : ℝ → ℝ)
    (hws : ∀ δ ∈ Set.Icc (0 : ℝ) 1, IsLeast (FeasS c fs δ) (ws δ))
    (hwd : ∀ δ ∈ Set.Icc (0 : ℝ) 1, IsLeast (FeasD c fd δ) (wd δ)) :
    StrictAntiOn (fun δ => expWage fd (wd δ)) (Set.Icc 0 1) ∧
      StrictAntiOn (fun δ => expWage fs (ws δ)) (Set.Icc 0 (deltaC fs)) ∧
      StrictMonoOn (fun δ => expWage fs (ws δ)) (Set.Icc (deltaC fs) 1) := by sorry

end TeamDiversity.WageGap

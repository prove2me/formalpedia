-- Prove2me | Theorems.Thm_ReliableFacilityLoc_Scenario_scenario_prob_first_operating
-- name    : ReliableFacilityLoc.Scenario.scenario_prob_first_operating
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:06.154423+00:00
-- url     : https://prove2.me/theorems/a3017b13-07ec-43ba-8da2-340ac2417be8
-- title:
--   Probability that the first operating facility in a list is $j(r)$
-- statement:
--   Let $j(0),\dots,j(r-1)$ be distinct regular facilities and let $j(r)$ be a facility (regular or the emergency facility $J$) different from all of them. Let
--   $$\Omega(i,r) = \{\omega\in\Omega : \delta_{j(r)\omega} = 1,\ \delta_{j(\ell)\omega} = 0\ \ \forall\, 0 \le \ell \le r-1\}$$
--   be the set of scenarios in which $j(0),\dots,j(r-1)$ have all failed and $j(r)$ operates. Then
--   $$\sum_{\omega\in\Omega(i,r)} p_\omega = (1-q_{j(r)})\prod_{\ell=0}^{r-1} q_{j(\ell)}.$$
--
--   This identity converts the scenario sum of (SSP) into the level-by-level probabilities of (RUFL) in both directions of the proof of Proposition 1.
--
--   **Formalization Note** The list $j(0),\dots,j(r-1)$ is a duplicate-free list of regular sites and $j(r)$ is any of the $J+1$ facilities not on it. For $j(r) = J$, $\delta_{J\omega} = 1$ and $q_J = 0$, so the right-hand side is $\prod_\ell q_{j(\ell)}$.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), Appendix A.1 (proof of Proposition 1), p. 33 (PDF 35), third equality of the unnumbered display; Ω(i, r) as defined on p. 34 (PDF 36)

import Definitions.Def_ReliableFacilityLoc_Scenario_SSP

open Finset

namespace ReliableFacilityLoc.Scenario

/-- **Scenario-probability identity** (Cui–Ouyang–Shen, UCTC-FR-2010-02 (Feb. 2010), A.1, proof of
Proposition 1, the third equality of the display on p. 33 (PDF 35), with `Ω(i, r)` as defined on
p. 34 (PDF 36)). Let `j(0), …, j(r-1)` be distinct regular facilities (the list `l`) and let `j(r)`
(the facility `k`, possibly the emergency facility `J`) differ from all of them. For
`Ω(i,r) = {ω ∈ Ω : δ_{j(r)ω} = 1, δ_{j(ℓ)ω} = 0 ∀ 0 ≤ ℓ ≤ r-1}`,
`Σ_{ω ∈ Ω(i,r)} p_ω = (1 - q_{j(r)}) Π_{ℓ=0}^{r-1} q_{j(ℓ)}`.

Formalization Note: `δ_Jω = 1` and `q_J = 0` for the emergency facility (pp. 8, 33), so for
`k = J` the right-hand side is `Π_ℓ q_{j(ℓ)}`. The distinctness hypotheses hold for the levels of a
(RUFL)-feasible assignment ((1b)–(1d)) and for the ordering of `N ∪ {J}` on p. 33; without them the
set `Ω(i,r)` can be empty while the right-hand side is not. -/
theorem scenario_prob_first_operating {I J R : ℕ} (D : Instance I J R) (l : List (Fin J))
    (hl : l.Nodup) (k : Fin (J + 1)) (hk : ∀ j ∈ l, j.castSucc ≠ k) :
    ∑ ω ∈ univ.filter (fun ω : FailureScenario J => delta ω k = true ∧ ∀ j ∈ l, ω j = false),
        D.scenarioProb ω =
      (1 - D.qExt k) * (l.map D.q).prod := by sorry

end ReliableFacilityLoc.Scenario

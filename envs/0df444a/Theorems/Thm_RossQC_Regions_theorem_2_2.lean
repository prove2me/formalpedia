-- Prove2me | Theorems.Thm_RossQC_Regions_theorem_2_2
-- name    : RossQC.Regions.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:18.539058+00:00
-- url     : https://prove2.me/theorems/131b8d35-eb83-4237-83d6-52fb22edb3ba
-- title:
--   Theorem 2.2 — the β-optimal inspect and revise regions are convex
-- statement:
--   In the general model of Ross's §2, let the $\beta$-optimal inspect region be the set of beliefs $P\in S$ with $V_\beta(P)=\sum_iP_iI_i+\beta\sum_iP_iV_\beta(e^i)$, and the $\beta$-optimal revise region the set of $P\in S$ with $V_\beta(P)=\sum_iP_iR_i+\beta V_\beta(e^0)$. Then
--   $$
--   \text{the }\beta\text{-optimal inspect region and the }\beta\text{-optimal revise region are convex subsets of } S.
--   $$
--
--   The produce region is not claimed to be convex; this asymmetry is what allows an optimal policy with four regions in the two-state model.
--
--   **Formalization Note** The regions are taken inside $S$, since $V_\beta$ is only meaningful on beliefs.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 589, Theorem 2.2; Definition of the regions, p. 588

import Mathlib
import Definitions.Def_RossQC_Regions_Model

namespace RossQC.Regions

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, p. 589, Theorem 2.2: "Both the β-optimal inspect and revise regions are
convex."

Under the standing hypotheses of §1–§2 (`Model.Valid`), the β-optimal inspect region and the
β-optimal revise region (Definition, p. 588: the beliefs `P ∈ S` at which inspecting, resp.
revising, attains the minimum in (1)) are convex subsets of `ι → ℝ`.

**Formalization Note.** The regions are subsets of the state space `S` (`Model.region`), as the
paper's `{P : …}` ranges over `S`. `V_β` is the limit of value iteration (`Model.Vβ`). -/
theorem theorem_2_2 {ι : Type*} [Countable ι] (M : Model ι) (hM : M.Valid) :
    Convex ℝ M.inspectRegion ∧ Convex ℝ M.reviseRegion := by sorry

end RossQC.Regions

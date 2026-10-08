-- Prove2me | Theorems.Thm_RossQC_Regions_optimality_equation
-- name    : RossQC.Regions.optimality_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:20.752712+00:00
-- url     : https://prove2.me/theorems/d1c239a8-0538-43a4-bcd5-14a9166d1a79
-- title:
--   §2, (1) — V_β exists as the limit of value iteration, is bounded, and is the unique bounded solution of the optimality equation
-- statement:
--   Consider the general model of Ross's §2: countably many underlying states, a stochastic transition matrix $(P_{ij})$, bounded costs $C_i,I_i,R_i$ and a discount factor $\beta\in(0,1)$. Let $S$ be the set of probability vectors on the states and $V^n$ the value iterates, with $V^0=0$.
--
--   1. For every $P\in S$ the sequence $V^n(P)$ converges; its limit is $V_\beta(P)$.
--   2. $V_\beta$ is bounded on $S$.
--   3. $V_\beta$ solves the optimality equation: for every $P\in S$,
--   $$
--   V_\beta(P)=\min\Big\{\sum_i P_iC_i+\beta V_\beta(TP);\ \sum_i P_iI_i+\beta\sum_i P_iV_\beta(e^i);\ \sum_i P_iR_i+\beta V_\beta(e^0)\Big\}.
--   $$
--   4. Every function $W$ that is bounded on $S$ and satisfies the same equation on $S$ coincides with $V_\beta$ on $S$.
--
--   The paper quotes this from Blackwell as "well known"; every structural result of the paper is derived from it.
--
--   **Formalization Note** Uniqueness is among functions bounded on $S$. The paper's companion clause, that a rule selecting a minimizer of the right side is $\beta$-optimal, is the definition of $\beta$-optimality used in this mission rather than a claim of this theorem.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 588, §2, (1)

import Mathlib
import Definitions.Def_RossQC_Regions_Model

namespace RossQC.Regions

open Filter Topology

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, §2, (1), p. 588 (unnumbered statement): "It is well known (see [1]) that
`V_β(P)` is the unique solution to (1)".

Under the standing hypotheses of §1–§2 (`Model.Valid`):

1. for every belief `P ∈ S` the value iterates `V^n(P)` converge (so `V_β(P)` is their limit);
2. `V_β` is bounded on `S`;
3. `V_β` satisfies the optimality equation (1) at every `P ∈ S`;
4. every function `W` that is bounded on `S` and satisfies (1) on `S` equals `V_β` on `S`.

**Formalization Note.** `V_β` is defined as the limit of value iteration from `V⁰ = 0`
(see `Model.Vβ`), not as an infimum over a policy class. Uniqueness is asserted in the class of
functions bounded on `S`, the setting of Blackwell [1]. The second half of the paper's sentence ("any
rule which … selects an action which minimizes the right side of (1) is β-optimal") is the convention
by which β-optimality is formalized elsewhere in this mission, not a claim of this theorem. -/
theorem optimality_equation {ι : Type*} [Countable ι] (M : Model ι) (hM : M.Valid) :
    (∀ P ∈ M.simplex, ∃ L : ℝ, Tendsto (fun n => M.valueIter n P) atTop (𝓝 L)) ∧
    (∃ B : ℝ, ∀ P ∈ M.simplex, |M.Vβ P| ≤ B) ∧
    (∀ P ∈ M.simplex, M.Vβ P = M.bellman M.Vβ P) ∧
    (∀ W : (ι → ℝ) → ℝ, (∃ B : ℝ, ∀ P ∈ M.simplex, |W P| ≤ B) →
      (∀ P ∈ M.simplex, W P = M.bellman W P) → ∀ P ∈ M.simplex, W P = M.Vβ P) := by sorry

end RossQC.Regions

-- Prove2me | Theorems.Thm_PriorityAlloc_DAFlex_h1_cutoff_respects_quota
-- name    : PriorityAlloc.DAFlex.h1_cutoff_respects_quota
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:09.616001+00:00
-- url     : https://prove2.me/theorems/e0a20277-9595-4d1b-927a-9a404dc1ff17
-- title:
--   Proof of Proposition H.1, p. 47 — under the priorities (H.1) the DA cutoff respects the quotas, D_j(z′) ≤ q_j
-- statement:
--   Let $M$ satisfy the standing assumptions, $y \in Y^M$, $G_t$ the priority law (H.1), and $q_j$ the left-hand side of (11). If $z' = z^{DA(M,G,q)}$ is the DA cutoff on $\Pi = [0,2]^n$, then
--   $$D_j(z') \le q_j \qquad \text{for every item } j \in [n].$$
--
--   The paper justifies this by the continuity of the demand function under the priority law (H.1), which has no atoms in the tie-breaker. Together with (H.4) it yields the contradiction in the proof of Proposition H.1.
-- source:
--   Shi, Optimal Priority-Based Allocation Mechanisms, SSRN manuscript 3425348 (June 2020; published Management Science 2022, doi:10.1287/mnsc.2020.3925), p. 47, proof of Proposition H.1, last sentence: 'the DA mechanism always respects the quotas if the demand function D_j defined in (A.2) is continuous'

import Mathlib
import Definitions.Def_PriorityAlloc_DAFlex_Model

namespace PriorityAlloc.DAFlex

open MeasureTheory Classical

variable {m n : ℕ}

/-- Proof of Proposition H.1, p. 47: under the priority law (H.1), whose demand function is
continuous, the DA cutoff respects the quotas: `D_j(z') ≤ q_j` for every item `j`. -/
theorem h1_cutoff_respects_quota (M : Market m n) (hM : M.Standing)
    (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y) (z : Fin n → ℝ)
    (hz : IsDACutoff M (h1Law y) (lhs11 M y) 2 z) :
    ∀ j, demand M (h1Law y) z j ≤ lhs11 M y j := by sorry

end PriorityAlloc.DAFlex

-- Prove2me | Theorems.Thm_ResourceScheduling_Chain_chainSchedule_of_threePartition
-- name    : ResourceScheduling.Chain.chainSchedule_of_threePartition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:27:02.436896+00:00
-- url     : https://prove2.me/theorems/d435f99f-786d-4818-acde-4aaca1a12694
-- title:
--   Proof of Theorem 7 ("if") — a 3-PARTITION solution gives a schedule with $C_{\max} = 2tb$
-- statement:
--   Let $t, b, a_1,\dots,a_{3t}$ be a valid 3-PARTITION instance ($b>0$, $\sum_j a_j = tb$, $\tfrac14 b < a_j < \tfrac12 b$), and consider the instance of $P2\mid res111, chain, p_j=1\mid C_{\max}$ constructed from it in the proof of Theorem 7: the chain $L$ of $2tb$ jobs alternating blocks of $b$ primed and $b$ unprimed jobs, and for each $j$ the chain $K_j \to K'_j$ of $a_j$ unprimed followed by $a_j$ primed jobs, the primed jobs requiring the single unit resource. If $\{1,\dots,3t\}$ can be partitioned into $t$ disjoint 3-element sets each summing to $b$, then the constructed instance has a feasible schedule with
--   $$C_{\max} = 2tb.$$
--
--   This is the "if" direction of the claim on which the proof of Theorem 7 rests.
--
--   **Formalization Note.** The schedule must be feasible in the model's sense: real start times, half-open execution intervals, the resource checked at every real time. For $t = 0$ the instance has no jobs and $C_{\max} = 0$.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 19, proof of Theorem 7 ("if" direction)

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_Constructions

namespace ResourceScheduling.Chain
theorem chainSchedule_of_threePartition (P : ThreePartition) (hP : P.Valid)
    (hS : P.HasSolution) :
    ∃ σ : Schedule P.chainInstance, σ.Feasible ∧ σ.cmax = ((2 * P.t * P.b : ℕ) : ℝ) := by sorry
end ResourceScheduling.Chain

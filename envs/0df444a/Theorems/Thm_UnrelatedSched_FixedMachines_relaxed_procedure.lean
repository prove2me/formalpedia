-- Prove2me | Theorems.Thm_UnrelatedSched_FixedMachines_relaxed_procedure
-- name    : UnrelatedSched.FixedMachines.relaxed_procedure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:28.007323+00:00
-- url     : https://prove2.me/theorems/ed629cca-9398-4ac4-a1bd-f648af91f041
-- title:
--   §3, p. 6 — the procedure $A_\varepsilon$ is a $(1+\varepsilon)$-relaxed decision procedure
-- statement:
--   Let $P$ be an $m\times n$ matrix of positive integer processing times, $\varepsilon>0$, and let $V$ be any vertex selector (an LP solver that returns a vertex of each feasible residual LP, and returns nothing only for an infeasible one). Then
--
--   1. the procedure $A_\varepsilon$ run with $V$ exists: there is a decision procedure $D$ that tries every admissible schedule of long assignments, rounds the vertex of the residual LP, and combines the result with the long assignments; and
--   2. every such procedure $D$ is a $(1+\varepsilon)$-relaxed decision procedure: on every deadline $d$ it either answers 'no', in which case no schedule has makespan at most $d$, or returns a schedule of makespan at most $(1+\varepsilon)d$.
--
--   In the paper: "We try all possible schedules of long assignments in this way, computing the remaining available time on each machine and applying the rounding procedure. Either we conclude that the instance is a 'no' instance, or we produce a schedule with makespan at most $(1+\varepsilon)d$."
--
--   **Formalization Note** The existence clause is where the Rounding Theorem (Theorem 1) enters: each vertex of a feasible residual LP can be rounded, within its support, to an (IP) solution. The paper applies Theorem 1 with $t=\varepsilon d$, which need not be an integer although Theorem 1 asks for $t\in\mathbb Z_+$; the proof of Theorem 1 does not use integrality. Running time is not formalized.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 6, Section 3, proof of Theorem 3; p. 5, definition of a ρ-relaxed decision procedure

import Mathlib
import Definitions.Def_UnrelatedSched_FixedMachines_LongAssignment
import Definitions.Def_UnrelatedSched_FixedMachines_BinarySearch

namespace UnrelatedSched.FixedMachines

/-- §3, p. 6: for every LP solver (vertex selector) `V`, the procedure `A_ε` run with `V` exists
(every vertex of a feasible residual LP can be rounded), and every procedure that is `A_ε` run
with `V` is a `(1 + ε)`-relaxed decision procedure: it either answers 'no', in which case no
schedule has makespan at most `d`, or produces a schedule with makespan at most `(1 + ε) d`. -/
theorem relaxed_procedure {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (hP : ∀ i j, 0 < P i j) (ε : ℝ) (hε : 0 < ε)
    (V : ℕ → (Fin n → Option (Fin m)) → Option (Matrix (Fin m) (Fin n) ℝ))
    (hV : IsVertexSelector P ε V) :
    (∃ D : ℕ → Option (Fin n → Fin m), IsAepsProcedure P ε V D) ∧
    ∀ D : ℕ → Option (Fin n → Fin m), IsAepsProcedure P ε V D →
      IsRelaxedDecisionProcedure P (1 + ε) D := by sorry

end UnrelatedSched.FixedMachines

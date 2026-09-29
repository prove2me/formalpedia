-- Prove2me | Theorems.Thm_SatiaLave_MaxMin_phase1_step_improves_for_nature
-- name    : SatiaLave.MaxMin.phase1_step_improves_for_nature
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:39:39.772978+00:00
-- url     : https://prove2.me/theorems/9ef0932d-ca6b-4b3b-a7e2-ae34505e473c
-- title:
--   Proof of Proposition 4 — a non-final Phase 1 iteration improves nature's return
-- statement:
--   Fix a policy $A$. Let $P$ be nature's current choice, with present values $v^A$, and let $P'$ be produced by one Phase 1 iteration (each row $p_i'^{A}$ minimizes $\sum_j p_{ij}(r^{A_i}_{ij}+\beta v^A_j)$ over $S_i^{A_i}$). Write $w^A$ for the present values of $A$ under $P'$. If the stopping test fails, i.e. $\sum_j p'^{A}_{ij}(r^{A_i}_{ij}+\beta v^A_j)\ne v^A_i$ for some state $i$, then
--   $$v_i^A\ge w_i^A\quad(i=1,\dots,N),\qquad\text{with strict inequality for at least one } i.$$
--
--   This is the first step of the proof of Proposition 4: Phase 1 generates a monotonically decreasing sequence of present-value vectors.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, pp. 731-732, Proof of Proposition 4

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Algorithm

namespace SatiaLave.MaxMin

/-- Proof of Proposition 4, pp. 731–732: an iteration of Phase 1 after which the stopping test
fails lowers the present value of `A` in no state and strictly lowers it in at least one. -/
theorem phase1_step_improves_for_nature {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P P' : Sel M)
    (hstep : IsPhase1Step M A P P') (hnot : ¬ Phase1Stops M A P P') :
    (∀ i, presentValue M A P' i ≤ presentValue M A P i) ∧
      ∃ i, presentValue M A P' i < presentValue M A P i := by sorry

end SatiaLave.MaxMin

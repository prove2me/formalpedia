-- Prove2me | Theorems.Thm_SingleMachinePrec_VariableCost_Supplement_theorem_4_2
-- name    : SingleMachinePrec.VariableCost.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:49:35.544468+00:00
-- url     : https://prove2.me/theorems/27fba85e-7313-438b-8a32-96872c9c8868
-- title:
--   Theorem 4.2 — a polynomial-time $4/3$-approximation for semiorder precedence constraints
-- statement:
--   An instance consists of $n$ jobs with nonnegative integer processing times $p_j$ and weights $w_j$ and a partial order $P$ of precedence constraints; a feasible schedule processes the jobs one at a time in an order $\sigma$ in which $i$ comes before $j$ whenever $(i,j)\in P$, $i\neq j$, and its cost is $\sum_j w_j C_j$, where $C_j$ is the completion time of job $j$.
--
--   If the precedence constraints form a semiorder (there are closed real intervals $[a_x,a_x+1]$ of unit length with $x<y$ exactly when $a_x+1<a_y$), then there is a deterministic polynomial-time algorithm that outputs a feasible schedule $\sigma$ with
--   $$\sum_j w_jC_j(\sigma)\ \le\ \frac43\,\mathrm{OPT}.$$
--   The input is the instance alone; no interval representation is supplied.
--
--   Semiorders are the unit-length subclass of interval orders, for which Theorem 6.2 gives the ratio $3/2$.
--
--   Differences from the source:
--   - encoding: polynomial-time algorithm (unspecified machine model) → one multi-stack Turing machine (published PolyTimeComputable, Mathlib TM2ComputableInPolyTime) on binary strings, running in time polynomial in the length of the input code; p_j, w_j in binary, the precedence relation as its n×n matrix, the output a code of the processing order; reason: standard machine model; binary numbers keep input sizes as in the paper
--   - encoding: cost at most α·OPT over all non-preemptive schedules → the output is a feasible processing order (permutation, no idle time) whose ∑ w_j C_j is at most α times the cost of every feasible processing order; reason: inserting idle time never decreases ∑ w_j C_j, so the optimum over idle-free orders is OPT; comparing with every feasible order avoids a default-valued minimum
--   - reading: the precedence constraints form a semiorder → the precedence relation given by its matrix satisfies IsSemiorderRel: a partial order with reals a_x such that x < y ↔ a_x + 1 < a_y; no representation of it is part of the input; reason: the theorem's input is the scheduling instance; recognition and construction are the algorithm's work (pp. 657–660 note they are polynomial)
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 658, Theorem 4.2

import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_Supplement_OrderClasses

set_option autoImplicit false

open QAlgorithms.Complexity

namespace SingleMachinePrec.VariableCost.Supplement

/-- Theorem 4.2 (p. 658): when the precedence constraints form a semiorder, there is a
deterministic polynomial-time `4/3`-approximation algorithm. The input is the instance with its
precedence matrix; no unit-interval representation is supplied. -/
theorem theorem_4_2 :
    HasPolyTimeApprox SchedInput.enc id (fun x => IsSemiorderRel x.Prec)
      (fun _ => 4 / 3) := by sorry

end SingleMachinePrec.VariableCost.Supplement

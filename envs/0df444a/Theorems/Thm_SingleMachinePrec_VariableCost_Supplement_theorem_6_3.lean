-- Prove2me | Theorems.Thm_SingleMachinePrec_VariableCost_Supplement_theorem_6_3
-- name    : SingleMachinePrec.VariableCost.Supplement.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:51:44.896347+00:00
-- url     : https://prove2.me/theorems/537f8dca-d974-48a0-af8c-85a632a8637f
-- title:
--   Theorem 6.3 — a polynomial-time $1.75$-approximation for precedence constraints of interval dimension at most 2
-- statement:
--   An instance consists of $n$ jobs with nonnegative integer processing times $p_j$ and weights $w_j$ and a partial order $P$ of precedence constraints; a feasible schedule processes the jobs one at a time in an order $\sigma$ in which $i$ comes before $j$ whenever $(i,j)\in P$, $i\neq j$, and its cost is $\sum_j w_j C_j$, where $C_j$ is the completion time of job $j$.
--
--   If the precedence constraints have interval dimension at most $2$ ($P=Q_1\cap Q_2$ for two interval orders $Q_1,Q_2$ on the jobs, possibly equal), then there is a deterministic polynomial-time algorithm that outputs a feasible schedule $\sigma$ with
--   $$\sum_j w_jC_j(\sigma)\ \le\ 1.75\,\mathrm{OPT}.$$
--   The input is the instance alone; no interval realizer $\{Q_1,Q_2\}$ is supplied.
--
--   This class strictly contains the interval orders of Theorem 6.2.
--
--   Differences from the source:
--   - encoding: polynomial-time algorithm (unspecified machine model) → one multi-stack Turing machine (published PolyTimeComputable, Mathlib TM2ComputableInPolyTime) on binary strings, running in time polynomial in the length of the input code; p_j, w_j in binary, the precedence relation as its n×n matrix, the output a code of the processing order; reason: standard machine model; binary numbers keep input sizes as in the paper
--   - encoding: cost at most α·OPT over all non-preemptive schedules → the output is a feasible processing order (permutation, no idle time) whose ∑ w_j C_j is at most α times the cost of every feasible processing order; reason: inserting idle time never decreases ∑ w_j C_j, so the optimum over idle-free orders is OPT; comparing with every feasible order avoids a default-valued minimum
--   - reading: the precedence constraints form a poset of interval dimension at most 2 → the precedence relation given by its matrix satisfies IntervalDimLeTwo: P = Q₁ ∩ Q₂ for two interval orders; no representation of it is part of the input; reason: the theorem's input is the scheduling instance; recognition and construction are the algorithm's work (pp. 657–660 note they are polynomial)
--   - reading: polynomial-time 1.75-approximation algorithm → a deterministic one; reason: the text before Theorem 6.3 (p. 660) obtains it "by using conditional probabilities", i.e. derandomized as in §6.1
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 660, Theorem 6.3

import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_Supplement_OrderClasses

set_option autoImplicit false

open QAlgorithms.Complexity

namespace SingleMachinePrec.VariableCost.Supplement

/-- Theorem 6.3 (p. 660): when the precedence constraints have interval dimension at most 2,
there is a deterministic polynomial-time `1.75`-approximation algorithm. The input is the
instance with its precedence matrix; no interval realizer is supplied. -/
theorem theorem_6_3 :
    HasPolyTimeApprox SchedInput.enc id (fun x => IntervalDimLeTwo x.Prec)
      (fun _ => 7 / 4) := by sorry

end SingleMachinePrec.VariableCost.Supplement

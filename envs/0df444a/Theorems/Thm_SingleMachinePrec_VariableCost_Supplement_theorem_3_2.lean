-- Prove2me | Theorems.Thm_SingleMachinePrec_VariableCost_Supplement_theorem_3_2
-- name    : SingleMachinePrec.VariableCost.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:47:48.498836+00:00
-- url     : https://prove2.me/theorems/0b5412f7-5a6d-4ee7-95f3-a40f62d7b7d7
-- title:
--   Theorem 3.2 — a polynomial-time $(2-2/k)$-approximation when the precedence constraints are given by a $k$-realizer
-- statement:
--   An instance consists of $n$ jobs with nonnegative integer processing times $p_j$ and weights $w_j$ and a partial order $P$ of precedence constraints; a feasible schedule processes the jobs one at a time in an order $\sigma$ in which $i$ comes before $j$ whenever $(i,j)\in P$, $i\neq j$, and its cost is $\sum_j w_j C_j$, where $C_j$ is the completion time of job $j$.
--
--   Suppose the precedence constraints $P$ form a partial order that is not a linear order, and are given together with a $k$-realizer $\{L_1,\dots,L_k\}$ of $P$: $k$ linear extensions such that every incomparable pair is reversed by at least one of them. Then there is a deterministic algorithm, running in time polynomial in the size of the whole input (the instance and the $k$ listed linear extensions), that outputs a feasible schedule $\sigma$ with
--   $$\sum_j w_jC_j(\sigma)\ \le\ \Bigl(2-\frac2k\Bigr)\,\mathrm{OPT}.$$
--
--   This is the dimension-theoretic form of Hochbaum's vertex-cover bound; Theorems 4.1 and 4.2 apply it to 3-realizers.
--
--   Differences from the source:
--   - encoding: polynomial-time algorithm (unspecified machine model) → one multi-stack Turing machine (published PolyTimeComputable, Mathlib TM2ComputableInPolyTime) on binary strings, running in time polynomial in the length of the input code; p_j, w_j in binary, the precedence relation as its n×n matrix, the output a code of the processing order; reason: standard machine model; binary numbers keep input sizes as in the paper
--   - encoding: cost at most α·OPT over all non-preemptive schedules → the output is a feasible processing order (permutation, no idle time) whose ∑ w_j C_j is at most α times the cost of every feasible processing order; reason: inserting idle time never decreases ∑ w_j C_j, so the optimum over idle-free orders is OPT; comparing with every feasible order avoids a default-valued minimum
--   - reading: precedence constraints given by a k-realizer → the input carries the precedence matrix and the k linear extensions as processing orders; k is part of the input and not a fixed constant; reason: "given by" means the realizer is supplied; time is polynomial in the complete input
--   - reading: Theorem 3.2 does not repeat that P is not a linear order → hypothesis that P is a partial order and not a linear order; reason: standing assumption of §3 (p. 656: "Let P = (N, P) be any poset that is not a linear order"); it makes k ≥ 2
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 657, Theorem 3.2 (with the standing assumption of §3, p. 656)

import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_Supplement_OrderClasses

set_option autoImplicit false

open QAlgorithms.Complexity

namespace SingleMachinePrec.VariableCost.Supplement

/-- Theorem 3.2 (p. 657): for instances whose precedence constraints `P` (a partial order that is
not a linear order, §3) are given together with a `k`-realizer `{L_1, …, L_k}`, there is a
deterministic polynomial-time `(2 - 2/k)`-approximation algorithm; time is polynomial in the
whole input, including the `k` listed linear extensions. -/
theorem theorem_3_2 :
    HasPolyTimeApprox RealizerInput.enc RealizerInput.inst
      (fun R => R.inst.IsPoset ∧ ¬ IsLinearRel R.inst.Prec ∧ R.IsRealizer)
      (fun R => 2 - 2 / (R.k : ℝ)) := by sorry

end SingleMachinePrec.VariableCost.Supplement

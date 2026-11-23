-- Prove2me | Theorems.Thm_SingleMachinePrec_VariableCost_Supplement_theorem_6_4
-- name    : SingleMachinePrec.VariableCost.Supplement.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:52:37.316923+00:00
-- url     : https://prove2.me/theorems/fc6e5475-7970-45b0-8dbe-107d30441b5c
-- title:
--   Theorem 6.4 — a polynomial-time $(2-2/f)$-approximation, $f=1+\max\{\min\{\Delta_D,\Delta_U\},1\}$
-- statement:
--   An instance consists of $n$ jobs with nonnegative integer processing times $p_j$ and weights $w_j$ and a partial order $P$ of precedence constraints; a feasible schedule processes the jobs one at a time in an order $\sigma$ in which $i$ comes before $j$ whenever $(i,j)\in P$, $i\neq j$, and its cost is $\sum_j w_j C_j$, where $C_j$ is the completion time of job $j$.
--
--   For arbitrary precedence constraints, let $\Delta_D$ (respectively $\Delta_U$) be the largest number of jobs strictly below (respectively strictly above) a single job, and
--   $$f=1+\max\{\min\{\Delta_D,\Delta_U\},1\}.$$
--   Then there is a deterministic polynomial-time algorithm that outputs a feasible schedule $\sigma$ with
--   $$\sum_j w_jC_j(\sigma)\ \le\ \Bigl(2-\frac2f\Bigr)\,\mathrm{OPT}.$$
--
--   The ratio is below $2$ whenever $\min\{\Delta_D,\Delta_U\}$ is bounded, e.g. $4/3$ for the posets with $\Delta_D=2$ used in the NP-hardness proof of Lenstra and Rinnooy Kan.
--
--   Differences from the source:
--   - encoding: polynomial-time algorithm (unspecified machine model) → one multi-stack Turing machine (published PolyTimeComputable, Mathlib TM2ComputableInPolyTime) on binary strings, running in time polynomial in the length of the input code; p_j, w_j in binary, the precedence relation as its n×n matrix, the output a code of the processing order; reason: standard machine model; binary numbers keep input sizes as in the paper
--   - encoding: cost at most α·OPT over all non-preemptive schedules → the output is a feasible processing order (permutation, no idle time) whose ∑ w_j C_j is at most α times the cost of every feasible processing order; reason: inserting idle time never decreases ∑ w_j C_j, so the optimum over idle-free orders is OPT; comparing with every feasible order avoids a default-valued minimum
--   - reading: polynomial-time (2 − 2/f)-approximation algorithm → a deterministic one; reason: the proof (p. 661) derandomizes the sampling "by using the classical method of conditional probabilities"
--   - encoding: Δ_D = max{deg_D(j) : j ∈ N}, undefined for N = ∅ → 0 for an instance without jobs (then f = 2 and the ratio is 1); reason: the empty instance has only the empty schedule, of cost 0
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 660, Theorem 6.4 (proof pp. 660–661)

import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_Supplement_OrderClasses

set_option autoImplicit false

open QAlgorithms.Complexity

namespace SingleMachinePrec.VariableCost.Supplement

/-- Theorem 6.4 (p. 660): for arbitrary precedence constraints there is a deterministic
polynomial-time `(2 - 2/f)`-approximation algorithm, where
`f = 1 + max{min{Δ_D, Δ_U}, 1}` and `Δ_D`, `Δ_U` are the maximum numbers of jobs strictly below,
respectively strictly above, a job. -/
theorem theorem_6_4 :
    HasPolyTimeApprox SchedInput.enc id (fun x => x.IsPoset)
      (fun x => 2 - 2 / ((1 + max (min (maxDegD x.Prec) (maxDegU x.Prec)) 1 : ℕ) : ℝ)) := by sorry

end SingleMachinePrec.VariableCost.Supplement

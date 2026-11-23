-- Prove2me | Theorems.Thm_SingleMachinePrec_VariableCost_Supplement_theorem_6_5
-- name    : SingleMachinePrec.VariableCost.Supplement.theorem_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:53:26.408816+00:00
-- url     : https://prove2.me/theorems/3600400c-ee3f-4739-b5d9-be7266b5e8a6
-- title:
--   Theorem 6.5 — a polynomial-time randomized $(2-2/(t/k))$-approximation for lexicographic sums of samplable components (corrected: exact on linear orders)
-- statement:
--   An instance consists of $n$ jobs with nonnegative integer processing times $p_j$ and weights $w_j$ and a partial order $P$ of precedence constraints; a feasible schedule processes the jobs one at a time in an order $\sigma$ in which $i$ comes before $j$ whenever $(i,j)\in P$, $i\neq j$, and its cost is $\sum_j w_j C_j$, where $C_j$ is the completion time of job $j$.
--
--   Let $\mathcal C$ be a class of posets with efficiently samplable realizers: one polynomial-time randomized procedure samples uniformly from a $k_Q$-fold multiset realizer of size $t_Q$ for every $Q\in\mathcal C$, counting repetitions. Consider instances whose precedence constraints form a lexicographic sum $\sum_{x\in(N,P)}(Y_x,Q_x)$, given by the outer poset $(N,P)$ and the modules $(Y_x,Q_x)$, all of whose components $i\in\mathcal P=\{P\}\cup\{Q_x\}$ lie in $\mathcal C$, and let
--   $$\frac tk=\max_{i\in\mathcal P}\frac{t_i}{k_i}.$$
--   Then there is a randomized polynomial-time algorithm whose every outcome is a feasible schedule and whose expected cost satisfies
--   $$\mathbb E\Bigl[\sum_j w_jC_j\Bigr]\ \le\ \Bigl(2-\frac2{t/k}\Bigr)\,\mathrm{OPT}$$
--   whenever the lexicographic sum is not a linear order; when it is a linear order, every outcome is optimal.
--
--   It extends the low-dimension results of §4 and §6 to posets built from such components.
--
--   Differences from the source:
--   - encoding: polynomial-time algorithm (unspecified machine model) → one multi-stack Turing machine (published PolyTimeComputable, Mathlib TM2ComputableInPolyTime) on binary strings, running in time polynomial in the length of the input code; p_j, w_j in binary, the precedence relation as its n×n matrix, the output a code of the processing order; reason: standard machine model; binary numbers keep input sizes as in the paper
--   - encoding: cost at most α·OPT over all non-preemptive schedules → the output is a feasible processing order (permutation, no idle time) whose ∑ w_j C_j is at most α times the cost of every feasible processing order; reason: inserting idle time never decreases ∑ w_j C_j, so the optimum over idle-free orders is OPT; comparing with every feasible order avoids a default-valued minimum
--   - correction: ratio 2 − 2/(t/k) on every instance → ratio 2 − 2/(t/k) when the sum is not a linear order; ratio 1 (every outcome optimal) when it is a linear order; reason: on a linear order every component may have t_i = k_i = 1, so t/k = 1 and the printed ratio is 0, false whenever OPT > 0 (e.g. one job with p = w = 1); the proof of Theorem 5.1 (p. 659) treats the linear order separately as trivial. On a non-linear sum some component has an incomparable pair, so t_i ≥ 2k_i and the printed ratio is ≥ 1 and unchanged. Exactness is stronger on linear instances whose printed factor exceeds 1.
--   - reading: precedence constraints form a lexicographic sum → the outer poset and the modules are part of the input; the jobs are numbered block by block; reason: the hypothesis names the decomposition and its components; the numbering is a relabelling the algorithm could compute from the supplied decomposition
--   - reading: components admit efficiently samplable realizers → one valid family of samplable realizers (uniform polynomial-time machines for a seed range and for sampling extensions) covers every component; reason: an algorithm for infinitely many inputs needs a uniform sampler; this samples the multiset distribution without requiring computation of its size or indexed access
--   - encoding: randomized algorithm; approximation in expectation → a seed drawn uniformly from {0, …, N−1}, N ≥ 1 computed in polynomial time; the average cost over the seeds is bounded; reason: uniform choice among the t members (p. 658) is a uniform index; equations (5)–(8) bound the expectation
--   - generalization: on linear-order sums with t/k > 2 the printed factor 2−2/(t/k) is greater than 1 → every output is optimal on all linear-order sums; reason: the unique feasible processing order is optimal; this exact branch strengthens the source inequality whenever its printed factor exceeds 1
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 661, Theorem 6.5; p. 659, proof of Theorem 5.1 (the linear-order case)

import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_Supplement_LexSum

set_option autoImplicit false

open QAlgorithms.Complexity

namespace SingleMachinePrec.VariableCost.Supplement

open Classical in
/-- Theorem 6.5 (p. 661): let `F` be a valid family of efficiently samplable realizers. For
instances whose precedence constraints form a lexicographic sum (given by its outer poset and
modules) all of whose components (the outer poset and every module) belong to the family's
class, there is a polynomial-time randomized algorithm whose expected cost is at most
`(2 - 2/(t/k))` times the optimum, `t/k = max_i t_i/k_i` over the components, whenever the sum is
not a linear order; when the sum is a linear order, every outcome is optimal. -/
theorem theorem_6_5 (F : SamplableRealizers) (hF : F.Valid) :
    HasPolyTimeRandApprox LexSumInput.enc LexSumInput.toSched
      (fun L => ∀ Q ∈ L.components, F.Cls Q)
      (fun L => if IsLinearRel L.toSched.Prec then 1 else 2 - 2 / LexSumInput.maxRatio F L) := by sorry

end SingleMachinePrec.VariableCost.Supplement

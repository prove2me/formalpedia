-- Prove2me | Theorems.Thm_ThreeSum19202796_threeSum_bound
-- name    : ThreeSum19202796.threeSum_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-22T08:28:10.47582+00:00
-- url     : https://prove2.me/theorems/541e3934-9bd7-4fbf-9a1d-edcf917b178e
-- title:
--   Deterministic 3SUM in $O(n^{1.9202796})$ word-RAM steps
-- statement:
--   The 3SUM problem asks, given $n$ integers, whether three distinct positions hold values summing to zero (equal values at different positions are allowed). It can be solved deterministically in $O(n^{4800699/2500000})$ word-RAM steps, where
--
--   $$
--   \frac{4800699}{2500000} = 1.9202796.
--   $$
--
--   More precisely: for every $\kappa$, there is a single finite deterministic word-RAM program $P$, a word-width bound $b$, and a time function $T(n) = O(n^{1.9202796})$, all independent of $n$, such that for every instance $x$ of $n$ integers of absolute value at most $n^\kappa$, the machine run on $x$ with word width $W \ge b(\lfloor \log_2 n\rfloor + 1)$ halts within $T(n)$ steps and accepts exactly when $x$ has a zero-sum triple at three distinct positions. This is `EndStatement.ThreeSum.SolvedInTime` applied to the rational $4800699/2500000$.
--
--   The construction is the ternary-radix, color-coding data structure of the published $O(n^{1.962})$ formalization, organized as a compiled machine word-RAM program whose runtime is certified combinatorially. The exponent is a numerical refinement chain: $1.962 \to 1.921 \to 1.9203 \to 1.9202796$, the last step by tighter logarithm and entropy intervals with certified strict margins; the largest certified principal cost is the bank term, at most $156432807976/81463563795 < 1.92027946$, and the exported target absorbs the residual $10^{-7}$ gaps.
--
--   **Formalization Note** This is the benchmark end statement exported as `Race.bound` in the referenced Lean 4 project; the proof is `ThreeSum.solvedInTime_4800699_2500000` in module `Submission/ThreeSum/TernaryFinalSolver.lean`. It improves the platform's previous best formalized exponents $1.962$ and $1.960614$.
-- source:
--   JoshuaQFEX/3sum-bound (Apache-2.0), commit eda5da36565f1ad5136cea39a2251945e040a2f5: https://github.com/JoshuaQFEX/3sum-bound/blob/eda5da36565f1ad5136cea39a2251945e040a2f5/Submission.lean ; proof: .../Submission/ThreeSum/TernaryFinalSolver.lean ; proof note docs/three_sum_bound_note.pdf. Construction and original formalization: c0ldzy17/three-sum-lean (1.962); margin refinement to 1.9203: fringewidth/three-sum-lean; numerical refinement to 4800699/2500000: Joshua Wharton (QFEX).

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSum19202796.threeSum_bound :
    EndStatement.ThreeSum.SolvedInTime ((4800699 : Rat) / 2500000) := by sorry

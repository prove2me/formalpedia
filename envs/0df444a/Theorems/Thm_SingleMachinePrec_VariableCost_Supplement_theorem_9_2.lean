-- Prove2me | Theorems.Thm_SingleMachinePrec_VariableCost_Supplement_theorem_9_2
-- name    : SingleMachinePrec.VariableCost.Supplement.theorem_9_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:54:53.816326+00:00
-- url     : https://prove2.me/theorems/a78261d4-98fb-4e73-b947-910277c0612f
-- title:
--   Theorem 9.2 — a scheduling PTAS implies randomized subexponential SAT algorithms
-- statement:
--   If the single-machine precedence scheduling problem $1|\mathrm{prec}|\sum_j w_jC_j$ has a polynomial-time approximation scheme, then SAT has randomized bounded-error algorithms with arbitrarily small positive runtime exponents:
--
--   $$\text{for every }\eta>0,\qquad T(n)\le 2^{n^\eta}\quad\text{for all sufficiently large }n.$$
--
--   For each exponent there is one finite machine, correct with probability at least $2/3$ on every input formula, halting on every random tape. The premise is a PTAS for the full weighted completion objective on all finite instances with nonnegative integer processing times and weights.
--
--   This is the paper's conditional exclusion of a PTAS; it is a companion theorem independent of the published goal Theorem 8.1.
--
--   Differences from the source:
--   - encoding: PTAS and SAT without a fixed binary syntax or machine model → one computable scheme with polynomial-time specializations at accuracies 1/(m+1); binary CNF SAT and finite multi-stack Turing machines; reason: a cofinal sequence of positive accuracies is equivalent to arbitrary positive accuracy; standard encodings differ polynomially, absorbed by the arbitrary exponent; the source exponent ε is renamed η
--   - reading: SAT solved by a probabilistic algorithm; the proof invokes a high-probability reduction → every formula is decided correctly with probability at least 2/3; runtime at most 2^(n^η) for all sufficiently large lengths and every η > 0; reason: high probability exceeds a fixed bounded-error threshold eventually; finite input exceptions can be decided separately, amplification gives the conventional 2/3 bound, and choosing a smaller exponent absorbs constants and polynomial overhead
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 667, Theorem 9.2 and its proof

import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_Supplement_Complexity

set_option autoImplicit false

namespace SingleMachinePrec.VariableCost.Supplement

/-- Theorem 9.2 (p. 667): a PTAS for single-machine precedence scheduling implies
randomized bounded-error SAT algorithms of runtime `2^(n^η)` for every η > 0.
“With high probability” in the cited reduction supplies bounded error; the constant
2/3 is the conventional amplified error bound, not a numerical claim about that reduction. -/
theorem theorem_9_2 : HasSchedulingPTAS → HasRandSubexpSAT := by sorry

end SingleMachinePrec.VariableCost.Supplement

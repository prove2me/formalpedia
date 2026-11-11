-- Prove2me | Theorems.Thm_PrefixMixLearn_Proper_theorem_e_1
-- name    : PrefixMixLearn.Proper.theorem_e_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:46:20.2204+00:00
-- url     : https://prove2.me/theorems/0a51b97a-1b0a-4595-beec-9d6689ea5988
-- title:
--   Theorem E.1 — a finite randomized comparison test with advantage ≥ d_TV(F_0,F_1) − ξ from prefix-conditional oracles
-- statement:
--   There is one fair-coin program $\mathrm{Test}$, an absolute constant $C$ and an exponent $c$ such that for every $d\ge1$, rational $0<\xi\le1$ and full-support laws $F_0,F_1$ on $\{0,1\}^d$, each supplied through its exact prefix-conditional oracle: for every input $x\in\{0,1\}^d$ and on every run, $\mathrm{Test}_\xi(x)$ outputs $0$ or $1$, makes at most $Cd^5\xi^{-4}\log(2d/\xi)$ oracle calls and has log-cost at most $(d+\lceil1/\xi\rceil+\text{input length}+2)^c$; and its acceptance kernel $e(x)=\Pr[\mathrm{Test}_\xi(x)=1]$ satisfies
--   $$E_{F_0}e-E_{F_1}e\ge d_{TV}(F_0,F_1)-\xi.$$
--   The test uses no density evaluations. It supplies the virtual anchors of the candidate generator.
--
--   Differences from the source:
--   - reading: for rational 0 < ξ ≤ 1 there is a finite randomized test Test_ξ … O(d⁵ξ⁻⁴ log(2d/ξ)) oracle calls and polynomial ordinary bit time → one program for all d, ξ, with ∃ C before d, ξ for the call bound and one exponent c for the log-cost; reason: the O-bound and 'polynomial' are uniform statements about one test procedure taking ξ as input
--   - encoding: F_0, F_1 each supplied through its exact fixed-prefix conditional sampling oracle → `pairOracle F0 F1`: query b :: h asks COND_{F_b} at h; reason: two oracles behind one query instruction
--   - encoding: the input x → input [d, num ξ, den ξ, x_1, …, x_d]; reason: input encoding
--   - encoding: "a prefix-conditional algorithm" (no machine is named; costs include bit operations, query writing, response processing, random bits, output length, input reading; learner randomness is fair bits) → a program of the fair-coin log-cost RAM `Machine` (instructions charged by bit lengths; `coin` draws one fair bit; `query` sends a 0/1 prefix to `condOracle P` and is charged for every cell read and written; `halt` for every output cell); a run's law is over the coins and the oracle replies; reason: the paper's model made explicit; one log-cost bound bounds every listed resource (calls, written and returned symbols, coins, bit time, output length)
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 36 (PDF 38), Theorem E.1, (E.1)

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws
import Definitions.Def_PrefixMixLearn_Proper_Machine

namespace PrefixMixLearn.Proper

/-- Theorem E.1 (conditional comparison without density access): one fair-coin program `Test`,
given `d ≥ 1`, rational `0 < ξ ≤ 1` and `x ∈ {0,1}^d`, with prefix-conditional access to two
full-support laws `F_0, F_1` on `{0,1}^d` (query `b :: h` asks `COND_{F_b}` at `h`), outputs `[0]`
or `[1]` on every run, makes `O(d⁵ ξ⁻⁴ log(2d/ξ))` calls and has log-cost polynomial in
`d, ξ⁻¹` and the input length on every run, for every `x`; and its acceptance kernel
`e(x) = Pr[Test_ξ(x) = 1]` satisfies `E_{F_0} e − E_{F_1} e ≥ d_TV(F_0, F_1) − ξ` (E.1). -/
theorem theorem_e_1 :
    ∃ (prog : Program) (C : ℝ) (c : ℕ),
      ∀ (d : ℕ), 1 ≤ d → ∀ (ξ : ℚ), 0 < ξ → ξ ≤ 1 →
      ∀ (F0 F1 : Cube d → ℝ), IsLaw F0 → FullSupport F0 → IsLaw F1 → FullSupport F1 →
        (∀ x : Cube d,
          HaltsWithin prog (pairOracle F0 F1) (testInput ξ x)
            (((d + ⌈1 / ξ⌉₊ + encLen (testInput ξ x) + 2 : ℕ) : ℝ) ^ c) ∧
          QueriesWithin prog (pairOracle F0 F1) (testInput ξ x)
            (C * (d : ℝ) ^ 5 * (ξ : ℝ) ^ (-4 : ℤ) * Real.log (2 * d / ξ)) ∧
          OutputsSatisfy prog (pairOracle F0 F1) (testInput ξ x) (fun o => o = [0] ∨ o = [1])) ∧
        tv F0 F1 - ξ ≤
          ∑ x, F0 x * outProb prog (pairOracle F0 F1) (testInput ξ x) (fun o => o = [1]) -
            ∑ x, F1 x * outProb prog (pairOracle F0 F1) (testInput ξ x) (fun o => o = [1]) := by sorry

end PrefixMixLearn.Proper

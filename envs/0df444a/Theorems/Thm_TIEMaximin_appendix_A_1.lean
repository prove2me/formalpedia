-- Prove2me | Theorems.Thm_TIEMaximin_appendix_A_1
-- name    : TIEMaximin.appendix_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:43:45.326849+00:00
-- url     : https://prove2.me/theorems/ffdb9967-0af6-4a82-935c-2e81c411a04a
-- title:
--   Appendix A.1 — the TPS is computable in polynomial time
-- statement:
--   There is one polynomial-time Turing machine that, given $n\ge1$ and nonnegative rational item values $u$ in binary, outputs the rational number $\mathrm{TPS}_n(u,M)$.
--
--   In particular the TPS of a rational valuation is rational, of polynomial encoding length. The mechanism's deterministic quantities start from this computation.
--
--   Differences from the source:
--   - reading: polynomially many rational operations, a rational share of polynomial encoding length → one machine with `Turing.TM2ComputableInPolyTime` on binary encodings, correct for all n ≥ 1, all m and all nonnegative rational u; reason: the standard Turing-machine reading; running time polynomial in the input length bounds the output length
--   - encoding: inputs → `encTPSIn (n, list of values)`; outputs on n = 0 or negative entries are unconstrained; reason: such inputs are outside the statement
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Appendix A.1, p.38

import Mathlib
import Definitions.Def_TIEMaximin_Shares
import Definitions.Def_TIEMaximin_Encoding

namespace TIEMaximin

/-- **Appendix A.1** (p.38). The TPS of a rational valuation is rational and is computable in
polynomial time from the binary encoding.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Appendix A.1, p.38: "For rational
inputs this uses polynomially many rational operations and produces a rational share of polynomial
encoding length."

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` with input encoding
`encTPSIn` and output encoding `encWRat`. One machine serves all `n` and `m`. Inputs with `n = 0`
or a negative entry may get any output. The polynomial-size bound of the page follows from the
running time. -/
theorem appendix_A_1 :
    ∃ algTPS : ℕ × List ℚ → ℚ,
      Nonempty (Turing.TM2ComputableInPolyTime encTPSIn encWRat algTPS) ∧
      ∀ (n m : ℕ) (u : Fin m → ℚ), 0 < n → (∀ g, 0 ≤ u g) →
        ((algTPS (n, List.ofFn u) : ℚ) : ℝ) = tps n (fun g => (u g : ℝ)) := by sorry

end TIEMaximin

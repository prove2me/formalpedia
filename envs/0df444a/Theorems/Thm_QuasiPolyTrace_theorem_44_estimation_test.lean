-- Prove2me | Theorems.Thm_QuasiPolyTrace_theorem_44_estimation_test
-- name    : QuasiPolyTrace.theorem_44_estimation_test
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:02.089213+00:00
-- url     : https://prove2.me/theorems/bb7d7d8c-df57-469f-8a3c-1c6b8ad1a9d6
-- title:
--   Proof of Theorem 44, estimation — one separating statistic gives a test from $\lceil4/\tau^2\rceil$ traces
-- statement:
--   Let $x,y\in\{0,1\}^n$, let $0<P\le p\le1$, let $i\le1$ and let $S$ be a statistic. If
--
--   $$
--   \big|x^{(S)}_{[i:n],P}-y^{(S)}_{[i:n],P}\big|\ge\tau>0,
--   $$
--
--   then $x$ and $y$ can be distinguished, each with probability at least $\tfrac23$, from $\lceil4/\tau^2\rceil$ independent traces of retention probability $p$.
--
--   The test pads each trace with simulated zeros for the positions $i,\dots,0$, thins it to retention probability $P$, and estimates the $0/1$-valued statistic by its empirical mean.
--
--   Differences from the source:
--   - generalization: simulate a P < p retention probability → 0 < P ≤ p; reason: P = p needs no thinning; the Lean statement covers the printed case P < p
--   - reading: estimate S + ℓ within < ½τ^{C^b}_base with probability ≥ 2/3 using 4·τ^{−2·C^b}_base samples; "the sample complexity of distinguishing x from y … is ≤ 4·τ^{−2·C^b}_base" → Distinguishes n (1 − p) ⌈4/τ²⌉ x y for a discrepancy τ of the (shifted) statistic S; reason: τ stands for τ_base^{C^b}; the estimate decides between x and y with probability ≥ 2/3 each way; a sample count is a natural number
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), proof of Theorem 44, pp.43–44 ("We thus estimate the statistic S+ℓ from traces…")

import Mathlib
import Definitions.Def_TraceReconstruction
import Definitions.Def_QuasiPolyTrace_stat
import Definitions.Def_QuasiPolyTrace_window
import Definitions.Def_QuasiPolyTrace_Distinguishes

namespace QuasiPolyTrace

open OAI.TraceReconstruction

/-- **Proof of Theorem 44, estimation step (a discrepancy in one statistic gives a two-sided test).**
Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), proof of Theorem 44, pp.43–44: "We thus estimate the statistic S+ℓ from traces to distinguish x from
y: pad traces by prepending with 0s when d − R − R′ < 1, and simulate a P < p retention probability from
the actual retention probability p traces by throwing out each bit i.i.d. with probability 1 − P/p.
Because a statistic is a 0/1-valued random variable, we can thus estimate the expected value of our
statistic S + ℓ to within error < ½τ^{C^b}_base with probability ≥ 2/3 using 4 · τ^{−2·C^b}_base samples
(from Chebyshev's inequality)."

Statement: let `x, y` be `n`-bit strings, `0 < P ≤ p ≤ 1`, `i ≤ 1` a window start and `S` a statistic.
If `|x^{(S)}_{[i:n],P} − y^{(S)}_{[i:n],P}| ≥ τ > 0`, then `⌈4/τ²⌉` traces of retention probability `p`
suffice to tell `x` from `y` with probability at least `2/3` each way.

**Formalization Note.**
* `τ` stands for `τ_base^{C^b}`, and `S` for the shifted statistic `S + ℓ` of the proof.
* The test sees only the `⌈4/τ²⌉` complete traces of `x` (or `y`) at retention probability `p`, i.e.
  deletion probability `1 − p` (`Distinguishes`); the padding zeros of the window and the thinning to
  `P` must be simulated, as in the paper.
* `P ≤ p` (the paper writes `P < p` here and "P bounded by … p" on p.43); `P = p` needs no thinning. -/
theorem theorem_44_estimation_test (n : ℕ) (x y : Word n) (p P : ℝ) (hP0 : 0 < P) (hPp : P ≤ p)
    (hp1 : p ≤ 1) (i : ℤ) (hi : i ≤ 1) (S : Finset ℤ) (τ : ℝ) (hτ : 0 < τ)
    (hdisc : τ ≤ |stat P (window (List.ofFn x) i) S - stat P (window (List.ofFn y) i) S|) :
    Distinguishes n (1 - p) ⌈4 / τ ^ 2⌉₊ x y := by sorry

end QuasiPolyTrace

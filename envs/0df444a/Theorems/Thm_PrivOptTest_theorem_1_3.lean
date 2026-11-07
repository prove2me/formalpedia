-- Prove2me | Theorems.Thm_PrivOptTest_theorem_1_3
-- name    : PrivOptTest.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:02.905186+00:00
-- url     : https://prove2.me/theorems/11199b75-3279-4895-828a-e79e5e94fa7f
-- title:
--   Theorem 1.3, p.4 — ε-private threshold testing: Õ(log log m/ε) in polynomial time, and Ω(log log m/ε) (corrected: log = log₂)
-- statement:
--   For thresholds on a finite domain $\mathcal X\subset\mathbb R$ with $|\mathcal X|=m$:
--
--   1. **(Upper bound.)** There is a universal $C>0$ such that whenever $m\ge4$, $\varepsilon\in(0,1]$, $\beta\in(0,1/3]$, $1\le t\le n$ and
--   $$t\ge C\,\frac{\log\log m}{\varepsilon}\Big(\log\frac1\beta+\log\frac{\log\log m}{\varepsilon}\Big)$$
--   (base 2), the interactive randomized algorithm $\mathcal A_{\mathrm{val\text{-}thr}}$ is an $\varepsilon$-DP tester for $\mathcal H_{\mathrm{thr}}$ with resolution $t$ and failure probability at most $\beta$.
--   2. **(Polynomial time.)** There is $K$ such that, on the same range of parameters, an explicit charged program returns on every outcome of the coins exactly the transcript and output of $\mathcal A_{\mathrm{val\text{-}thr}}$, within $K\,(n\log_2m/\beta)^K$ unit-cost steps (real arithmetic, comparisons, logarithms, ceilings, bit operations, memory and coin reads).
--   3. **(Lower bound.)** There are $c>0$ and $m_0$ such that for $m\ge m_0$, every $\varepsilon>0$ and every $t\le n$, every $\varepsilon$-DP tester with resolution $t$ for $\mathcal H_{\mathrm{thr}}$ has $t\ge c\log\log m/\varepsilon$.
--
--   The optimal resolution of private threshold testing is thus $\tilde\Theta(\log\log m/\varepsilon)$, exponentially below the $\Theta(\log m/\varepsilon)$ of one-way or private-learning approaches.
--
--   Differences from the source:
--   - correction: log in the condition on t → log₂; reason: under natural logarithms the statement is false: at m = 4, ε = 1, β = 1/3 the right-hand side is negative (ln ln 4 ≈ 0.327), so t = n = 2 is allowed, k = 1, and Algorithm 2 outputs Far on a Match input with probability ≥ 0.47 > 1/3; log₂ is the paper’s convention in §E and in T = ⌈log₂ b⌉
--   - reading: "provided n, t ≳ (log log m/ε) log(log log m/ε)" with Definition 1.2’s 0.9 → Theorem 3.12’s hypothesis for every β ∈ (0, 1/3], failure probability β; reason: Theorem 1.3 is the informal version of Theorem 3.12; β = 1/10 gives Definition 1.2, and the condition on n follows from n ≥ t
--   - reading: "polynomial-time algorithm" → clause (T): an explicit charged program equal to the protocol on every coin outcome, within K (n log₂ m/β)^K unit-cost steps; reason: the paper names no machine; messages are real Laplace samples, so only a unit-cost real model applies; a bound in log m is the stronger of the two readings, and poly(m, n, 1/β) follows from it
--   - reading: the algorithm on X → avalThr: ranks lifted by ψ_A, ψ_B, blocks of ⌊t/2⌋ records, Algorithm 2 with n := ⌊t/2⌋; reason: §1.4.2 (p.9), Lemma 3.5 and Remark 3.6 (p.16)
--   - generalization: lower bound for ε ∈ (0,1] and t ∈ [n] → every ε > 0 and every t ≤ n; reason: Theorem 3.1 holds for every ε > 0; t = 0 is vacuous; specializes to the source
--   - encoding: multisets over X → sequences Fin n → X; reason: a multiset protocol is a sequence protocol ignoring order
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 1.3, p.4; Theorem 3.12, p.21; Theorem 3.1, p.14; Algorithm 2, p.20

import Mathlib
import Definitions.Def_PrivOptTest_IsTester
import Definitions.Def_PrivOptTest_algo2
import Definitions.Def_PrivOptTest_avalThrProg

namespace PrivOptTest

/-- **Theorem 1.3** (p.4), in the strength of Theorems 3.12 (p.21) and 3.1 (p.14). For thresholds on a
finite domain `X ⊂ ℝ` of size `m`:

* (U) there is a universal `C` such that, whenever `t ≥ C (log log m/ε)(log(1/β) + log(log log m/ε))`,
  `ε ∈ (0, 1]`, `β ∈ (0, 1/3]`, `1 ≤ t ≤ n`, `m ≥ 4`, the interactive randomized algorithm `A_val-thr`
  (Algorithm 2) is an ε-DP tester with resolution `t` for `H_thr` with failure probability at most `β`;
* (T) it runs in polynomial time: an explicit charged program `avalThrProg` returns, on every outcome of
  the coins, exactly the transcript and output of `A_val-thr`, within `K (n log m/β)^K` steps;
* (L) there are `c > 0`, `m₀` such that every ε-DP tester with resolution `t ≤ n` requires
  `t ≥ c log log m/ε`, for every `ε > 0`.

Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 1.3, p.4; Theorem 3.12, p.21; Theorem 3.1, p.14; Algorithm 2, p.20.

**Formalization Note.** `log = log₂` (with natural logarithms Theorem 3.12 is false at `m = 4`). The
condition on `n` of Theorem 3.12 is implied. Time is counted in the unit-cost real model: one tick per
real arithmetic operation, comparison, `ln`, `⌈·⌉`, bit operation, array read or write and coin read;
coins are random-access read-only tapes, and `tapeOf ω` reads the protocol's own coins. The bound has no
`ε`. -/
theorem theorem_1_3 :
    (∃ C : ℝ, 0 < C ∧ ∀ (X : Finset ℝ) (n t : ℕ) (ε β : ℝ), 4 ≤ X.card → 1 ≤ t → t ≤ n →
      0 < ε → ε ≤ 1 → 0 < β → β ≤ 1 / 3 →
      C * (Real.logb 2 (Real.logb 2 X.card) / ε) *
          (Real.logb 2 (1 / β) + Real.logb 2 (Real.logb 2 X.card / ε)) ≤ t →
      IsTester (avalThr X n t ε β) (HthrOn X) ε t β) ∧
    (∃ K : ℕ, ∀ (X : Finset ℝ) (n t : ℕ) (ε β : ℝ), 4 ≤ X.card → 1 ≤ t → t ≤ n →
      0 < ε → ε ≤ 1 → 0 < β → β ≤ 1 / 3 →
      ∀ (SA SB : Fin n → ↥X) (ω : (avalThr X n t ε β).Coins),
        ((avalThrProg X t ε β SA SB (tapeOf ω)).run 0).1.toResult =
            avalThrResult X t ε β SA SB ω ∧
          (((avalThrProg X t ε β SA SB (tapeOf ω)).run 0).2 : ℝ) ≤
            K * ((n : ℝ) * Real.logb 2 X.card / β) ^ K) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ (X : Finset ℝ) (ε : ℝ) (n t : ℕ), m₀ ≤ X.card → 0 < ε → t ≤ n →
      ∀ Pr : Protocol (Fin n → ↥X) Outcome, IsTester Pr (HthrOn X) ε t (1 / 10) →
        c * Real.logb 2 (Real.logb 2 X.card) / ε ≤ t) := by sorry

end PrivOptTest

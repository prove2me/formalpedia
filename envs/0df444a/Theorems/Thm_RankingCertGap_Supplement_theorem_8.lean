-- Prove2me | Theorems.Thm_RankingCertGap_Supplement_theorem_8
-- name    : RankingCertGap.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:00:35.616393+00:00
-- url     : https://prove2.me/theorems/8252f81b-2cb2-48d9-b6f1-fc2e290428a0
-- title:
--   Theorem 8 — large regular-degree values, gap scale, and optimizer convergence
-- statement:
--   For every integer $d\ge2$,
--   $$
--   \widetilde\gamma(d)\ge1-\left(1-\frac1d\right)^d
--   =1-\frac1e+\frac1{2ed}+O(d^{-2}).
--   $$
--   As $d\to\infty$ through the integers,
--   $$
--   \widetilde\Gamma(d)=1-\frac1e+\left(\frac1{2e}+o(1)\right)\frac{(\log d)^2}{d^2},
--   \qquad \widetilde\gamma(d)=1-\frac1e+o(1),
--   $$
--   $$
--   \widetilde\Delta(d)=o(1),
--   \qquad \liminf_{d\to\infty}d\widetilde\Delta(d)\ge\frac1{2e}.
--   $$
--   Moreover, every sequence $f_d\in\mathcal F$ satisfying $\widetilde\Gamma(d)-\widetilde\chi(f_d;d)\to0$ obeys
--   $$
--   \|f_d-f^\star_\infty\|_1\to0,
--   \qquad f^\star_\infty(y)=e^{y-1}.
--   $$
--
--   The result separates the scale of the certifiable regularity improvement from the larger $1/d$ certifying gap and identifies the only possible limiting profile of asymptotically optimal certificates.
--
--   **Formalization Note** The sharp capacity expansion is the equivalent normalized limit. The $L^1$ norm is the Lebesgue integral on $[0,1]$.
--
--   Differences from the source:
--   - encoding: $O(d^{-2})$ in the expansion of $1-(1-1/d)^d$ → an explicit absolute constant and integer threshold; reason: this is the definition of the remainder bound
--   - encoding: $(1/(2e)+o(1))(\log d)^2/d^2$ → the normalized limit $(\widetilde\Gamma(d)-(1-1/e))d^2/(\log d)^2\to1/(2e)$; reason: the forms are equivalent for integer $d\to\infty$
--   - encoding: $o(1)$, $\liminf$, and $L^1([0,1])$ convergence → filter limits, an eventual lower bound for every positive error, and the Lebesgue integral of the absolute difference; reason: these are their standard literal meanings and the eventual form avoids a junk real `liminf` on an unbounded sequence
--   - encoding: profiles on $[0,1]$ → total real profiles compared only in $L^1([0,1])$; reason: the extension changes no source value
--   - encoding: a sequence $(f_d)$ over positive integer degrees → a zero-based natural-number sequence with every term in $\mathcal F$; reason: adding the unused finite initial term does not affect either limit and every source sequence has such an extension
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Theorem 8, pp.10–11, eqs. (28)–(32)

import Mathlib
import Definitions.Def_RankingCertGap_Supplement_Objects

set_option autoImplicit false

open Filter Topology

namespace RankingCertGap.Supplement

/-- **Theorem 8 (Large regular degree).** Xu, arXiv:2610.17545 (held file sha256 75896dd9…),
Theorem 8, pp.10–11, eqs. (28)–(32). This includes the finite-degree lower bound and its
second-order expansion, the sharp normalized capacity asymptotic, convergence of competitiveness
and the gap, the `lim inf` lower bound, and `L¹` convergence of every asymptotically optimal profile
sequence.

**Formalization Note.** Equation (29) is represented by the normalized limit
`(Γ̃(d) - (1-1/e)) d²/(log d)² → 1/(2e)`, exactly equivalent to its printed
`(1/(2e)+o(1))(log d)²/d²` form. The `O(d⁻²)` in (28) is an explicit absolute constant and
threshold. Equation (32) quantifies over the entire sequence before assuming asymptotic optimality. -/
theorem theorem_8 :
    (∀ d : ℕ, 2 ≤ d →
      1 - (1 - 1 / (d : ℝ)) ^ d ≤ gammaC (regular d)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      |(1 - (1 - 1 / (d : ℝ)) ^ d) -
          (1 - 1 / Real.exp 1 + 1 / (2 * Real.exp 1 * d))| ≤ C / (d : ℝ) ^ 2) ∧
    Tendsto
      (fun d : ℕ =>
        (GammaC classF (regular d) - (1 - 1 / Real.exp 1)) * (d : ℝ) ^ 2 /
          (Real.log d) ^ 2)
      atTop (nhds (1 / (2 * Real.exp 1))) ∧
    Tendsto (fun d : ℕ => gammaC (regular d)) atTop (nhds (1 - 1 / Real.exp 1)) ∧
    Tendsto (fun d : ℕ => gapC classF (regular d)) atTop (nhds 0) ∧
    (∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ d : ℕ in atTop,
        1 / (2 * Real.exp 1) - epsilon ≤ (d : ℝ) * gapC classF (regular d)) ∧
    (∀ f : ℕ → ℝ → ℝ, (∀ d, f d ∈ classF) →
      Tendsto
        (fun d : ℕ => GammaC classF (regular d) - chiC (f d) (regular d))
        atTop (nhds 0) →
      Tendsto (fun d : ℕ => l1Dist (f d) expProfile) atTop (nhds 0)) := by sorry

end RankingCertGap.Supplement

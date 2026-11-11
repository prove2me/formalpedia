-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_tail_decrement
-- name    : SubadditiveProphet1456.Quarter.tail_decrement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:57.37063+00:00
-- url     : https://prove2.me/theorems/0fdce9ea-d931-4e0b-bdb8-03e00386cf52
-- title:
--   Lemma A.1 — Uniform logistic decrement of the score tail
-- statement:
--   With the standing setup $0<\theta<1$, a feasible $\mathrm{LP}(\theta)$ solution, and any RSG family supported on $\{0,\ldots,N\}^m$ satisfying (16), there is a single positive universal constant $c$ such that, for every item $j$ and every $1\le h<N$,
--   $$
--   Q_j(h)-Q_j(h+1)\ge cQ_j(h)(1-Q_j(h)).
--   $$
--   The constant is the explicit integral witness from Lemma A.3, fixed before all instances and depths. The height range is empty at $N=1$, as in the source. This decrement interface supplies the exponential score-tail estimate.
--
--   Differences from the source:
--   - encoding: Finite items and nonempty finite buyer type supports in fixed arrival order → Zero-based Fin indices and type supports Fin (k+1), with positive type probabilities; reason: Relabeling covers every source instance, including empty item or buyer sets; zero-probability labels are omitted from support
--   - encoding: There exists a positive universal c, with an explicit witness in the proof of Lemma A.3 → The explicit integral witness tailConstant, with positivity asserted and no instance parameters; reason: This selects the paper proof's own constant uniformly before all instances
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.31, PDF p.32, Lemma A.1.

import Definitions.Def_SubadditiveProphet1456_Quarter_CapHeight
import Definitions.Def_SubadditiveProphet1456_Quarter_Machine

open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace SubadditiveProphet1456.Quarter

theorem tail_decrement :
    0 < tailConstant ∧
    ∀ (n m : ℕ) (I : Instance n m) (θ : ℝ) (x : Fractional I)
      (N : ℕ) (φ : RSG I),
      0 < θ → θ < 1 → Feasible I θ x → 1 ≤ N →
      DistributionalEquation I x N φ →
      ∀ (j : Fin m) (h : ℕ), 1 ≤ h → h < N →
        tailConstant * Q I φ j h * (1-Q I φ j h) ≤ Q I φ j h-Q I φ j (h+1) := by sorry

end SubadditiveProphet1456.Quarter

-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_exponential_tail
-- name    : SubadditiveProphet1456.Quarter.exponential_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:52.914949+00:00
-- url     : https://prove2.me/theorems/92590dff-8b60-4880-a313-b3b1f46fcf3d
-- title:
--   Lemma 4.2 — Universal exponential score-tail bound
-- statement:
--   There is a positive constant $c$, explicitly the universal integral witness in Lemma A.3, independent of every instance, cap and score family. For every $0<\theta<1$, feasible $x$, integer $N\ge1$, and any capped integer RSG family satisfying equation (16) with the induced tentative laws and independent same-law references, let $Q_j(h)=\sum_i\Pr[b_{ij}\ge h]$. Then, for every item $j$,
--   $$
--   Q_j(N)\le\frac{\theta}{1-\theta}(1+c)^{-(N-1)}.
--   $$
--   The claim is uniform over all solutions of the distributional equation, rather than restricted to CapHeight. It includes $N=1$. This bound controls the loss from cap ties.
--
--   Differences from the source:
--   - encoding: Finite items and nonempty finite buyer type supports in fixed arrival order → Zero-based Fin indices and type supports Fin (k+1), with positive type probabilities; reason: Relabeling covers every source instance, including empty item or buyer sets; zero-probability labels are omitted from support
--   - encoding: There exists a positive universal c, with an explicit witness in the proof of Lemma A.3 → The explicit integral witness tailConstant, with positivity asserted and no instance parameters; reason: This selects the paper proof's own constant uniformly before all instances
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.12, PDF p.13, Lemma 4.2.

import Definitions.Def_SubadditiveProphet1456_Quarter_CapHeight
import Definitions.Def_SubadditiveProphet1456_Quarter_Machine

open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace SubadditiveProphet1456.Quarter

theorem exponential_tail :
    0 < tailConstant ∧
    ∀ (n m : ℕ) (I : Instance n m) (θ : ℝ) (x : Fractional I)
      (N : ℕ) (φ : RSG I),
      0 < θ → θ < 1 → Feasible I θ x → 1 ≤ N →
      DistributionalEquation I x N φ →
      ∀ j : Fin m, Q I φ j N ≤ θ/(1-θ)/(1+tailConstant)^(N-1) := by sorry

end SubadditiveProphet1456.Quarter

-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_lemma_2_4
-- name    : UnconditionalKLS.Dunkl.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T20:08:40.347408+00:00
-- url     : https://prove2.me/theorems/0c4d03aa-0350-4aae-8d5d-d7f80d6c8251
-- title:
--   Lemma 2.4 — Lipschitz transport with squared constant
-- statement:
--   Let $\nu$ be any probability measure on $\mathbb R^n$, let $L>0$ and let $T:\mathbb R^n\to\mathbb R^n$ be $L$-Lipschitz. For the pushforward $\nu'=T_\#\nu$,
--   $$C_P(\nu')\le L^2C_P(\nu).$$
--   The statement includes singular probability measures and nonsmooth, noninvertible maps, with infinite constants allowed. Its Poincaré constant uses the local metric slope for arbitrary laws; on the absolutely continuous laws of this paper this agrees almost everywhere with the gradient convention. It transfers constants through the actual measurable pushforward, retaining the squared Lipschitz factor.
--
--   Differences from the source:
--   - reading: ambient gradients of locally Lipschitz tests for an arbitrary probability law → the standard pointwise local metric slope, agreeing with gradients on absolutely continuous laws; reason: for the law on the x-axis in R² the test f(x,y)=|y| is nondifferentiable on a set of full measure; the slope convention keeps every law and resolves the undefined gradient
--   - encoding: functions on real Euclidean space with the paper’s analytic domains → Fin n coordinates, L² equivalence classes and canonical graph/form completions; extended nonnegative infima; reason: these represent the same objects; positive dimensions are retained and finite integrals are guarded
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 12, Lemma 2.4; contextual domains in Appendix A, pp. 31–38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Domains

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
theorem lemma_2_4 {n : ℕ} (ν : Measure (Space n)) [IsProbabilityMeasure ν]
    (T : Space n → Space n) (L : ℝ) (hL : 0 < L)
    (hT : LipschitzWith (Real.toNNReal L) T) :
    poincare (Measure.map T ν) ≤ ENNReal.ofReal (L^2) * poincare ν := by sorry
end UnconditionalKLS.Dunkl

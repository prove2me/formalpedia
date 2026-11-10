-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_lemma_2_5
-- name    : UnconditionalKLS.Dunkl.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T20:08:49.429199+00:00
-- url     : https://prove2.me/theorems/ebc30419-aaa7-4a62-8e9e-3ebea5deef9e
-- title:
--   Lemma 2.5 — scale comparison in both directions
-- statement:
--   Let $\mu=e^{-V}dx$ be any unconditional log-concave probability law on $\mathbb R^n$, allowing extended convex potentials and bounded supports. For $0<S'\le S$, define $\eta_S=(T_S^{-1})_\#\mu$ using the coordinate map (2.1). Then
--   $$C_P(\eta_{S'})\le C_P(\eta_S)\le\frac{S}{S'}C_P(\eta_{S'}).$$
--   Both comparisons refer to the same original measure and the specified family of transports. The optimal constants may be infinite; extended nonnegative arithmetic handles this without changing the assertion. This permits comparison across scales with the exact linear ratio, without assuming smoothness or isotropy of the original law.
--
--   Differences from the source:
--   - encoding: functions on real Euclidean space with the paper’s analytic domains → Fin n coordinates, L² equivalence classes and canonical graph/form completions; extended nonnegative infima; reason: these represent the same objects; positive dimensions are retained and finite integrals are guarded
--   - generalization: the original law in the temporary smooth phase (2.5) → any normalized unconditional extended convex potential, including nonsmooth and bounded-support laws; reason: the scale-map comparison uses no potential regularity; every law satisfying (2.5) is included
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 12, Lemma 2.5; contextual domains in Appendix A, pp. 31–38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Domains

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
theorem lemma_2_5 {n : ℕ} (hn : 0 < n) (V : Potential n) (S S' : ℝ)
    (hS' : 0 < S') (hSS' : S' ≤ S) :
    poincare (sourceLaw S' V.law) ≤ poincare (sourceLaw S V.law) ∧
    poincare (sourceLaw S V.law) ≤ ENNReal.ofReal (S/S') * poincare (sourceLaw S' V.law) := by sorry
end UnconditionalKLS.Dunkl

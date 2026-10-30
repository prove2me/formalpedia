-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_compact_fiber_lowerSemicontinuous
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.compact_fiber_lowerSemicontinuous
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:43:54.596392+00:00
-- url     : https://prove2.me/theorems/fedcd462-25f2-47ea-96a8-73a1333ed93e
-- title:
--   Lemma 4.3: compact-fiber infimum preserves lower semicontinuity
-- statement:
--   Let $X$ be any compact metric space, let $c\in\mathbb R$, and let $F:X\times X\to[c,\infty]$ be jointly lower semicontinuous. Then
--   $$x\longmapsto\inf_{y\in X}F(x,y)$$
--   is lower semicontinuous. Infima are extended-real infima, and no nonemptiness assumption on $X$ is needed. This isolates the compact-fiber topological step used in the continuity analysis.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 14, Lemma 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.14, Lemma 4.3: the compact-fiber infimum of a jointly lower
semicontinuous function bounded below by finite c remains lower semicontinuous.
The space may be empty. EReal infima retain infinity. -/
theorem compact_fiber_lowerSemicontinuous {X : Type*} [MetricSpace X] [CompactSpace X]
    (c : ℝ) (F : X × X → EReal) (hlower : ∀ z, (c : EReal) ≤ F z)
    (hF : LowerSemicontinuous F) :
    LowerSemicontinuous (fun x => ⨅ y, F (x,y)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end

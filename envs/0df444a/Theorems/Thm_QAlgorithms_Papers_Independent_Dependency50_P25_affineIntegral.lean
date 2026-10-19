-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P25_affineIntegral
-- name    : QAlgorithms.Papers.Independent.Dependency50.P25.affineIntegral
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:17:53.075067+00:00
-- url     : https://prove2.me/theorems/492c9465-c369-4294-a24a-de7efa115348
-- title:
--   Affine integral identity for lower semicontinuous extended costs
-- statement:
--   Let $A$ be a closed, bounded, convex subset of a separable real Banach space $E$, and let $f:A\to[-\infty,+\infty]$ be affine and lower semicontinuous. For every Borel probability measure $\mu$ on $A$,
--
--   $$
--   f\!\left(\int_A x\,\mu(dx)\right)=\int_A f(x)\,\mu(dx).
--   $$
--
--   The barycenter is Bochner-integrated and the scalar cost is extended-integrated. Constant $+\infty$ and $-\infty$ functions are included. This identifies the expectation of a lower semicontinuous affine cost with its value at the barycenter.
-- source:
--   On properties of the space of quantum states and their application to construction of entanglement monotones, arXiv:0804.1515v4, PDF p. 31, Corollary A-1: affine integral identity

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P25

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P25

/-- Corollary A-1 (affine integral identity), arXiv:0804.1515v4,
PDF p.31, Eq.(28). Lower semicontinuity is the sole regularity assumption;
constant positive and negative infinite costs are retained. The vector
barycenter is Bochner, while its extended cost is integrated by its parts. -/
theorem affineIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (A : Set E) (hclosed : IsClosed A) (hbounded : Bornology.IsBounded A)
    (f : E → EReal) (haffine : extendedAffineOn A f)
    (hlower : LowerSemicontinuous (fun x : A => f x))
    (mu : Measure A) [IsProbabilityMeasure mu] :
    f (banachBarycenter mu) = extendedIntegral mu (fun x : A => f x) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P25

end

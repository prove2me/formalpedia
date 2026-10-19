-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P25_discreteJensen
-- name    : QAlgorithms.Papers.Independent.Dependency50.P25.discreteJensen
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:16:46.77391+00:00
-- url     : https://prove2.me/theorems/12235af5-bd62-429c-ad1c-03f9556dc285
-- title:
--   Discrete Jensen inequality for upper-bounded extended costs
-- statement:
--   Let $A$ be a closed, bounded, convex subset of a real Banach space $E$. Let $f:A\to[-\infty,+\infty]$ be convex and bounded above by a finite real constant. For any sequence $(x_i)_{i\ge0}$ in $A$ and weights $\pi_i\ge0$ with $\sum_i\pi_i=1$, the vector series converges in norm and
--
--   $$
--   f\!\left(\sum_{i\ge0}\pi_i x_i\right)\le\sum_{i\ge0}\pi_i f(x_i).
--   $$
--
--   The right side is the extended signed sum, with zero-weight contributions equal to zero; it may equal $-\infty$. This extends finite Jensen convexity to arbitrary countable ensembles without any continuity or measurability requirement on $f$.
-- source:
--   On properties of the space of quantum states and their application to construction of entanglement monotones, arXiv:0804.1515v4, PDF p. 31, Proposition A-1: discrete Jensen inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P25

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P25

/-- Proposition A-1 (discrete Jensen inequality), arXiv:0804.1515v4,
PDF p.31. The domain is closed, convex and bounded in an arbitrary real
Banach space; the cost can take negative infinity and is only upper bounded.
Normalized nonnegative weights guarantee convergence of the vector series.
Indexing by `Nat` includes finite ensembles by appending zero weights. -/
theorem discreteJensen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : Set E) (hclosed : IsClosed A)
    (hbounded : Bornology.IsBounded A) (f : E → EReal)
    (hconvex : extendedConvexOn A f)
    (hupper : ∃ M : ℝ, ∀ x ∈ A, f x ≤ (M : EReal))
    (x : ℕ → E) (hx : ∀ i, x i ∈ A)
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (htotal : HasSum w 1) :
    f (∑' i : ℕ, w i • x i) ≤ extendedSeries w (fun i => f (x i)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P25

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P09_classical_noEvent
-- name    : QAlgorithms.Papers.Independent.Next46.P09.classical_noEvent
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:01:34.128866+00:00
-- url     : https://prove2.me/theorems/3b718238-63b7-4107-9dfd-2180b61e403c
-- title:
--   Classical no-event evolution has exponential holding weights
-- statement:
--   Let $X$ be a countable set, possibly empty, and let $(T_t)_{t\ge0}$ be a strongly continuous positive contraction semigroup on the real space $\ell^1(X)$. Assume that $T_t\delta_x$ is a nonnegative multiple of a point mass for every $t\ge0$ and $x\in X$, where $\delta_x$ denotes the normalized mass at $x$. There is a function $\mu:X\to[0,\infty)$ such that
--
--   $$T_t\delta_x=e^{-t\mu(x)}\delta_x\qquad(t\ge0,\ x\in X).$$
--
--   Thus a no-event evolution cannot move its starting atom. The rates can vanish and need not be uniformly bounded.
-- source:
--   Unbounded generators of dynamical semigroups, arXiv:1707.02266v1, PDF p. 3, Section II.A, classical no-event form (3)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P09

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P09

universe u v

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass IsTraceClass traceNormValue operatorTrace IsPositive)

open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

/-- Section II.A, arXiv:1707.02266v1, PDF p.3, (3).
The rates may be zero and may be unbounded as x varies. X may be empty. -/
theorem classical_noEvent {X : Type u} [Countable X] (T : ClassicalNoEventSemigroup X) :
    ∃ mu : X → NNReal, ∀ (t : NNReal) (x : X),
      T.maps t (pointMass x) =
        Real.exp (-(t : ℝ) * (mu x : ℝ)) • pointMass x := by sorry

end QAlgorithms.Papers.Independent.Next46.P09

end

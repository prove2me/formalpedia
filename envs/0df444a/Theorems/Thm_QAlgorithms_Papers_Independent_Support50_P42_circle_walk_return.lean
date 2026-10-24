-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_circle_walk_return
-- name    : QAlgorithms.Papers.Independent.Support50.P42.circle_walk_return
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:17:11.310037+00:00
-- url     : https://prove2.me/theorems/4b37e0bc-e4d0-4f50-a1df-a7f1285f9f69
-- title:
--   Positive-time return for an arbitrary circular random walk
-- statement:
--   On a probability space let $X_0,X_1,\ldots$ be independent, identically distributed measurable real-valued steps, with no finite-support or density restriction. Let $Z_m=\{\sum_{i=0}^{m-1}X_i\}$ be the fractional part of the partial sum, representing the walk on the circle. For every $\epsilon>0$,
--
--   $$\Pr\!\left(\exists m\ge1:\ Z_m\in[0,\log_2(1+\epsilon)]\right)=1.$$
--
--   Time zero is explicitly excluded. Real representatives include every Borel step distribution on the circle. This is the positive-time recurrence assertion used in the source's batching argument.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 8, §III: positive-time return of the circular random walk

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.8: positive-time circular return for any IID step law. Real
representatives cover all Borel laws on R/Z. Neither finite support nor a
density is assumed. Time zero cannot witness the conclusion. -/
theorem circle_walk_return {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (X : ℕ → Omega → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X mu)
    (hlaw : ∀ i, Measure.map (X i) mu=Measure.map (X 0) mu)
    (epsilon : ℝ) (he : 0<epsilon) :
    mu {w | ∃ m : ℕ, 0 < m ∧ circlePosition X m w∈Set.Icc 0 (Real.logb 2 (1+epsilon))}=1 := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end

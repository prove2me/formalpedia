-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_lemma_5_2
-- name    : QAlgorithms.Papers.Independent.Support50.P12.lemma_5_2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:38:55.540107+00:00
-- url     : https://prove2.me/theorems/b2448b30-7a93-4d25-b4e6-c1536b4bbc24
-- title:
--   Lemma 5.2
-- statement:
--   Let $I$ be a finite index set, let $x_i\ge0$ be pairwise distinct, let $t_i>0$ be pairwise distinct, and let $f$ be any complex-valued function on the interpolation points.
--
--   There are complex coefficients $c_j$ such that
--
--   $$f(x_i)=\sum_{j\in I}\frac{c_j}{x_i+t_j}\qquad(i\in I).$$
--
--   The empty family gives the empty interpolation identity. This supplies resolvent interpolation on finite spectra.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 25, Lemma 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Lemma 5.2, PDF p.25: injective interpolation points, distinct positive poles;
the empty index set yields the empty identity. -/
theorem lemma_5_2 {L : Type} [Fintype L] (x t : L → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hxi : Function.Injective x)
    (ht : ∀ i, 0 < t i) (hti : Function.Injective t) (f : ℝ → ℂ) :
    ∃ c : L → ℂ, ∀ i, f (x i) = ∑ j, c j / ((x i + t j : ℝ) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end

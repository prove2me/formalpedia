-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_corollary_A_5
-- name    : QAlgorithms.Papers.Independent.Support50.P12.corollary_A_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:56:03.263167+00:00
-- url     : https://prove2.me/theorems/f2c9ab65-db21-4d81-b3e5-59acef482fc5
-- title:
--   Corollary A.5
-- statement:
--   Let $A,B$ be positive semidefinite operators on a nonzero finite-dimensional complex Hilbert space. Operator powers are zero on kernels; scalar trace powers have their usual real-power convention.
--
--   One has
--
--   $$\operatorname{Tr}A^\alpha B^{1-\alpha}\le(\operatorname{Tr}A)^\alpha(\operatorname{Tr}B)^{1-\alpha}\quad(0\le\alpha\le1).$$
--
--   If $A^0\le B^0$, the inequality is reversed for every $\alpha\ge1$, and
--
--   $$\exists\alpha>0,\ \alpha
--   e1:\ \operatorname{Tr}A^\alpha B^{1-\alpha}=(\operatorname{Tr}A)^\alpha(\operatorname{Tr}B)^{1-\alpha}\iff A=cB\text{ for some }c\ge0.$$
--
--   Zero operators are included. The endpoint inequalities do not have a proportionality characterization.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 45, Corollary A.5

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

/-- Corollary A.5, PDF pp.45–46: both full exponent ranges and the 'some positive
order other than one' equality characterization, including zero operators. -/
theorem corollary_A_5 [Nonempty I] (X Y : Mat I) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (∀ a ∈ Icc (0 : ℝ) 1, tr (supportPower X a * supportPower Y (1 - a)) ≤
      Real.rpow (tr X) a * Real.rpow (tr Y) (1 - a)) ∧
    (Supports X Y → ∀ a ≥ (1 : ℝ), tr (supportPower X a * supportPower Y (1 - a)) ≥
      Real.rpow (tr X) a * Real.rpow (tr Y) (1 - a)) ∧
    (Supports X Y →
      ((∃ a : ℝ, 0 < a ∧ a ≠ 1 ∧ tr (supportPower X a * supportPower Y (1 - a)) =
        Real.rpow (tr X) a * Real.rpow (tr Y) (1 - a)) ↔
        ∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • Y)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end

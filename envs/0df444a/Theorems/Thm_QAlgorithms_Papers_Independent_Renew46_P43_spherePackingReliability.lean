-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_spherePackingReliability
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.spherePackingReliability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:43:59.212437+00:00
-- url     : https://prove2.me/theorems/90c8810a-e9af-428b-b0b3-d3a083e338b3
-- title:
--   Corollary II.21: For 0≤R≤C(W), with possible exception of the leftmost finite Esp value: E(R)≤Esp(R)=max_P Esp(R,P).
-- statement:
--   Let $W$ be a finite stationary channel and $0\le R\le C(W)$. Define $E_{\rm sp}(R)=\sup_P E_{\rm sp}(R,P)$. Exclude exactly the case where this value is finite and every smaller nonnegative rate has infinite sphere-packing bound. The maximizing input law is attained.
--
--   $$
--   E(R)\le E_{\rm sp}(R)=\max_P E_{\rm sp}(R,P).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 36, Corollary II.21

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Corollary II.21, PDF p.36: exclude exactly a finite leftmost sphere-packing
value with every smaller nonnegative rate infinite, not all zero or positive rates. -/
theorem spherePackingReliability {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (W : FiniteChannel a (fullAlgebra d hd)) (R : ℝ) (hR : 0 ≤ R) (hcap : R ≤ W.capacity)
    (hnotleftmost : ¬ (sphereBound W R ≠ ⊤ ∧
      ∀ r : ℝ, 0 ≤ r → r < R → sphereBound W r = ⊤)) :
    reliability W R ≤ sphereBound W R ∧
    ∃ P : PMF (Fin a), sphereBound W R = sphereExponent W R P := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_entropyIncrease
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.entropyIncrease
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:00:49.816041+00:00
-- url     : https://prove2.me/theorems/691a0cef-08f7-4c69-9885-c9748238d17a
-- title:
--   Theorem A.10: For CP-unital phi:Y→X,psi:X→A and Tr phi(B)≤Tr B for positive B, H(psi∘phi)≥H(psi).
-- statement:
--   Fix a normalized ambient state. Let $\phi:Y\to X$ and $\psi:X\to A$ be CP-unital Heisenberg operations, with $\operatorname{Tr}\phi(T)\le\operatorname{Tr}T$ for every positive $T$. Define $H(\psi)=H(\psi_*\rho)$. Composition reverses the physical state-map order; compatibility is not assumed.
--
--   $$
--   H(\psi\circ\phi)\ge H(\psi).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 70, Theorem A.10

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

/-- Theorem A.10, PDF pp.70-71: composition reverses state-map order. No
compatibility assumption is needed for these composable quantum operations. -/
theorem entropyIncrease {Y X A : IntrinsicSystem} (F : IntrinsicOperation Y X) (G : IntrinsicOperation X A)
    (htrace : TraceNonincreasing F) (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hrho : A.IsState rho) :
    viewedEntropy Y (G.map.comp F.map) rho ≥ viewedEntropy X G.map rho := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end

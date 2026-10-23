-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_classicalConditionalEntropy
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.classicalConditionalEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:09:52.775202+00:00
-- url     : https://prove2.me/theorems/5eac87e6-8d20-4361-983a-76a36c954e47
-- title:
--   Theorem A.20: Compatible quantum operations phi:X→A,psi:Y→A with X OR Y commutative satisfy H(phi|psi)≥0.
-- statement:
--   Fix a normalized state on a finite ambient algebra and compatible CP-unital operations $\phi:\mathcal X\to A$ and $\psi:\mathcal Y\to A$. Commutativity is a disjunction on the entire domain algebras, not on one pair of operators.
--
--   $$
--   \mathcal X\text{ or }\mathcal Y\text{ commutative}\Longrightarrow H(\phi\mid\psi)\ge0.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 74, Theorem A.20

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

/-- Theorem A.20, PDF p.74: at least one entire domain algebra is commutative;
no nonnegativity hypothesis is imposed on the desired conditional entropy. -/
theorem classicalConditionalEntropy {X Y A : IntrinsicSystem} (E : IntrinsicOperation X A) (F : IntrinsicOperation Y A)
    (hcompat : CommutingImages E.map F.map)
    (hclassical : (Function.Injective X.block) ∨ (Function.Injective Y.block))
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : A.IsState rho) :
    0 ≤ intrinsicConditionalEntropy X Y E.map F.map rho := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end

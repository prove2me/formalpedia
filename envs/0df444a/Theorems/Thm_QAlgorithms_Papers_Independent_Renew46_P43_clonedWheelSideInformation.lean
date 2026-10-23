-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_clonedWheelSideInformation
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.clonedWheelSideInformation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:56:28.627121+00:00
-- url     : https://prove2.me/theorems/1b33f104-82fb-4260-b25b-cfcb72ec1981
-- title:
--   cloned-wheel-side-information: For cloned wheel, A1 alone can be recovered exactly from free A2 at decoder with no message.
-- statement:
--   For the cloned-wheel ensemble, suppose the decoder receives the second copy as free quantum side information and must recover only the first local state. For every block length $n$, there is a CPTP map $T_n$ from a one-dimensional message and the second word to the desired first word. The side information may be consumed.
--
--   $$
--   T_n([0]\otimes\pi_{x_1}\otimes\cdots\otimes\pi_{x_n})=\pi_{x_1}\otimes\cdots\otimes\pi_{x_n},\qquad\dim M=1.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 57, cloned-wheel-side-information

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

/-- Unnumbered cloned-wheel side-information example, PDF p.57. The second copy
may be consumed. A one-dimensional message and the identity recovery suffice for
A1 alone; recovery of both copies is deliberately not the task in this model. -/
theorem clonedWheelSideInformation (n : ℕ) :
    ∃ T : Superop (Fin 1 × (Fin n → Fin 2)) (Fin n → Fin 2), IsChannel T ∧
      ∀ w : Fin n → Fin 4,
        T (Matrix.kronecker (1 : Matrix (Fin 1) (Fin 1) ℂ)
          (wordTensor (fun i => pureDensity (wheelVector (w i))))) =
          wordTensor (fun i => pureDensity (wheelVector (w i))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end

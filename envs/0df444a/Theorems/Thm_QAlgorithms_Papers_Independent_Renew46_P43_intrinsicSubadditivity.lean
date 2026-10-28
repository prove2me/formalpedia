-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_intrinsicSubadditivity
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.intrinsicSubadditivity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:00:08.833113+00:00
-- url     : https://prove2.me/theorems/66ff9cfc-19af-4b67-b145-309e842f5ba6
-- title:
--   Theorem A.9: Compatible A1,A2,A3 satisfy subadditivity H(A1A2)≤H(A1)+H(A2), SSA H(A1A2A3)+H(A2)≤H(A1A2)+H(A2A3), equivalently conditional subad
-- statement:
--   Fix one normalized ambient state and finite intrinsic C*-algebras. Subsystem inclusions are unital star embeddings and distinct named compatible images commute elementwise, with central overlap allowed. Entropies are those of trace-adjoint restrictions; $H(XY)$ is entropy on the generated algebra, equivalently the spectrum-preserving pullback by multiplication. Mutual information is $I(X;Y)=H(X)+H(Y)-H(XY)$. In subalgebra processing the larger algebras are compatible. In operation processing the maps $\psi_i$ are compatible CP-unital maps and $\phi_i$ arbitrary composable CP-unital maps, not necessarily homomorphisms.
--
--   $$
--   H(A_1A_2)\le H(A_1)+H(A_2),\qquad H(A_1A_2A_3)+H(A_2)\le H(A_1A_2)+H(A_2A_3).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 70, Theorem A.9

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

/-- Theorem A.9, PDF p.70: subadditivity and strong subadditivity for genuinely
compatible intrinsic subalgebras, which may overlap in the center. -/
theorem intrinsicSubadditivity {A : Fin 3 → IntrinsicSystem} {C : IntrinsicSystem}
    (E : ∀ i, Embedding (A i) C) (rho : Matrix (Fin C.dim) (Fin C.dim) ℂ)
    (hrho : C.IsState rho) (hcompat : ∀ i j, i ≠ j → CommutingImages (E i).map (E j).map) :
    familyEntropy A (fun i => (E i).map) rho {0,1} ≤
      familyEntropy A (fun i => (E i).map) rho {0} + familyEntropy A (fun i => (E i).map) rho {1} ∧
    familyEntropy A (fun i => (E i).map) rho Finset.univ +
      familyEntropy A (fun i => (E i).map) rho {1} ≤
      familyEntropy A (fun i => (E i).map) rho {0,1} +
      familyEntropy A (fun i => (E i).map) rho {1,2} := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end

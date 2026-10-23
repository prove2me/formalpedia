-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_operationInformation
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.operationInformation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:05:45.985641+00:00
-- url     : https://prove2.me/theorems/6adb63a8-8df8-4a9d-8b83-5407e471418e
-- title:
--   A.14-operation-processing: For compatible CP-unital psi_i:A_i→A and CP-unital phi_i:A_i_prime→A_i, I(psi1∘phi1:psi2∘phi2)≤I(psi1:psi2).
-- statement:
--   Fix one normalized ambient state and finite intrinsic C*-algebras. Subsystem inclusions are unital star embeddings and distinct named compatible images commute elementwise, with central overlap allowed. Entropies are those of trace-adjoint restrictions; $H(XY)$ is entropy on the generated algebra, equivalently the spectrum-preserving pullback by multiplication. Mutual information is $I(X;Y)=H(X)+H(Y)-H(XY)$. In subalgebra processing the larger algebras are compatible. In operation processing the maps $\psi_i$ are compatible CP-unital maps and $\phi_i$ arbitrary composable CP-unital maps, not necessarily homomorphisms.
--
--   $$
--   I(\psi_1\circ\phi_1;\psi_2\circ\phi_2)\le I(\psi_1;\psi_2).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 72, A.14-operation-processing

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

/-- General operation processing following Theorem A.14, PDF p.72: the local
operations are CP-unital maps, not assumed multiplicative. -/
theorem operationInformation {X Y Xnew Ynew A : IntrinsicSystem}
    (E : IntrinsicOperation X A) (F : IntrinsicOperation Y A) (hcompat : CommutingImages E.map F.map)
    (i : IntrinsicOperation Xnew X) (j : IntrinsicOperation Ynew Y)
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : A.IsState rho) :
    intrinsicMutualInformation Xnew Ynew (E.map.comp i.map) (F.map.comp j.map) rho ≤
      intrinsicMutualInformation X Y E.map F.map rho := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end

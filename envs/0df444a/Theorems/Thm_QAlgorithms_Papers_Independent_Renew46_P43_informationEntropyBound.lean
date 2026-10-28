-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_informationEntropyBound
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.informationEntropyBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:09:09.978145+00:00
-- url     : https://prove2.me/theorems/77d40dd9-288c-4176-9945-20a426bf5221
-- title:
--   Theorem A.19: I(Xalg:Yalg)≤2min{H(Xalg),H(Yalg)} for compatible algebras.
-- statement:
--   Fix one normalized ambient state and finite intrinsic C*-algebras. Subsystem inclusions are unital star embeddings and distinct named compatible images commute elementwise, with central overlap allowed. Entropies are those of trace-adjoint restrictions; $H(XY)$ is entropy on the generated algebra, equivalently the spectrum-preserving pullback by multiplication. Mutual information is $I(X;Y)=H(X)+H(Y)-H(XY)$. In subalgebra processing the larger algebras are compatible. In operation processing the maps $\psi_i$ are compatible CP-unital maps and $\phi_i$ arbitrary composable CP-unital maps, not necessarily homomorphisms.
--
--   $$
--   I(X;Y)\le2\min\{H(X),H(Y)\}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 74, Theorem A.19

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

/-- Theorem A.19, PDF p.74. The factor two is essential even for an EPR pair. -/
theorem informationEntropyBound {X Y A : IntrinsicSystem} (E : Embedding X A) (F : Embedding Y A)
    (hcompat : CommutingImages E.map F.map) (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hrho : A.IsState rho) :
    intrinsicMutualInformation X Y E.map F.map rho ≤
      2 * min (viewedEntropy X E.map rho) (viewedEntropy Y F.map rho) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end

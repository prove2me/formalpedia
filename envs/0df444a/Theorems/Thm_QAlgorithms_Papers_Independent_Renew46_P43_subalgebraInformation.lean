-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_subalgebraInformation
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.subalgebraInformation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:05:03.621321+00:00
-- url     : https://prove2.me/theorems/dd9264b5-843b-4390-ad81-928708b9a2f8
-- title:
--   A.14-subalgebra-monotonicity: If Xalg⊆Xprime,Yalg⊆Yprime and larger algebras compatible, I(Xalg:Yalg)≤I(Xprime:Yprime).
-- statement:
--   Fix one normalized ambient state and finite intrinsic C*-algebras. Subsystem inclusions are unital star embeddings and distinct named compatible images commute elementwise, with central overlap allowed. Entropies are those of trace-adjoint restrictions; $H(XY)$ is entropy on the generated algebra, equivalently the spectrum-preserving pullback by multiplication. Mutual information is $I(X;Y)=H(X)+H(Y)-H(XY)$. In subalgebra processing the larger algebras are compatible. In operation processing the maps $\psi_i$ are compatible CP-unital maps and $\phi_i$ arbitrary composable CP-unital maps, not necessarily homomorphisms.
--
--   $$
--   \mathcal X\subseteq\mathcal X',\ \mathcal Y\subseteq\mathcal Y'\Longrightarrow I(\mathcal X;\mathcal Y)\le I(\mathcal X';\mathcal Y').
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 72, A.14-subalgebra-monotonicity

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

/-- Subalgebra monotonicity following Theorem A.14, PDF p.72. The larger
subalgebras commute; the smaller ones are their actual included subalgebras. -/
theorem subalgebraInformation {X Y Xbig Ybig A : IntrinsicSystem}
    (E : Embedding Xbig A) (F : Embedding Ybig A) (hcompat : CommutingImages E.map F.map)
    (i : Embedding X Xbig) (j : Embedding Y Ybig)
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : A.IsState rho) :
    intrinsicMutualInformation X Y (E.map.comp i.map) (F.map.comp j.map) rho ≤
      intrinsicMutualInformation Xbig Ybig E.map F.map rho := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end

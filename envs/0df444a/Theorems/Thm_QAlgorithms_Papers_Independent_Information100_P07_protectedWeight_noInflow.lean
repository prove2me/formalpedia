-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_protectedWeight_noInflow
-- name    : QAlgorithms.Papers.Independent.Information100.P07.protectedWeight_noInflow
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:42:56.998957+00:00
-- url     : https://prove2.me/theorems/51ae1a8c-311b-438d-babe-b65f7850cc70
-- title:
--   Unnumbered: protected weight is conserved and no exterior inflow occurs
-- statement:
--   Let CPTP channels with given Kraus families interconvert normalized states $\rho,\sigma$ and both protect the range of an orthogonal projector $P$ by scaled unitaries, with probability weights. Put $Q=I-P$. Their adjoint images of $P$ dominate $P$, and
--   $$\operatorname{Tr}(P\rho)=\operatorname{Tr}(P\sigma).$$
--   For each forward Kraus operator $K_i$, $PK_iQ\rho QK_i^\dagger P=0$ and $PK_iQ\rho P=0$; the reverse channel satisfies the corresponding equations with input $\sigma$. Each channel separately transports the retained block, exterior block and coherence block to the corresponding target block. Thus $[\rho,P]=0$ if and only if $[\sigma,P]=0$. If $P$ is a product rectangle and both restrictions are product unitary, their unnormalized retained blocks are LU equivalent.
--
--   No inflow is input-specific; the off-diagonal Kraus block need not vanish as an operator.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 16, Unnumbered: protected weight is conserved and no exterior inflow occurs

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF p.16, Eq.(S32): weight and input-specific no inflow in both directions. -/
theorem protectedWeight_noInflow {m n : ℕ} (A : Fin m → Joint) (B : Fin n → Joint)
    (p : Fin m → ℝ) (q : Fin n → ℝ) (rho sigma P : Joint)
    (hA : IsKrausFamily A) (hB : IsKrausFamily B)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) (hP : IsProjection P)
    (hforward : krausApply A rho = sigma) (hreverse : krausApply B sigma = rho)
    (hprotectA : Protects A (operatorRange P) p) (hprotectB : Protects B (operatorRange P) q) :
    (P * rho).trace = (P * sigma).trace ∧
    ((∑ i, (A i)ᴴ * P * A i) - P).PosSemidef ∧ ((∑ i, (B i)ᴴ * P * B i) - P).PosSemidef ∧
    (∑ i, (A i)ᴴ * P * A i) - P = ∑ i, (1-P) * (A i)ᴴ * P * A i * (1-P) ∧
    (∑ i, (B i)ᴴ * P * B i) - P = ∑ i, (1-P) * (B i)ᴴ * P * B i * (1-P) ∧
    (∀ i, P * A i * (1-P) * rho * (1-P) * (A i)ᴴ * P = 0 ∧ P * A i * (1-P) * rho * P = 0) ∧
    (∀ i, P * B i * (1-P) * sigma * (1-P) * (B i)ᴴ * P = 0 ∧ P * B i * (1-P) * sigma * P = 0) ∧
    krausApply A (P*rho*P) = P*sigma*P ∧ krausApply B (P*sigma*P) = P*rho*P ∧
    krausApply A ((1-P)*rho*(1-P)) = (1-P)*sigma*(1-P) ∧
    krausApply B ((1-P)*sigma*(1-P)) = (1-P)*rho*(1-P) ∧
    krausApply A (P*rho*(1-P)) = P*sigma*(1-P) ∧ krausApply B (P*sigma*(1-P)) = P*rho*(1-P) ∧
    (rho*P = P*rho ↔ sigma*P = P*sigma) ∧
    (∀ U V : Local, IsProjection U → IsProjection V → P = Matrix.kronecker U V →
      ProductProtects A U V p → ProductProtects B U V q → LU (P*rho*P) (P*sigma*P)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end

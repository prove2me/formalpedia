-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_spectralEntropyEquality
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.spectralEntropyEquality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:02:26.658967+00:00
-- url     : https://prove2.me/theorems/b620249b-1440-4a0d-8cdd-1c62a868d928
-- title:
--   A.10-equality: For full spectral resolution rho=sum lambda_i p_i, entropy is preserved by restriction to the generated algebra or any intermediat
-- statement:
--   Let $\rho=\sum_i\lambda_i p_i$ be a full fine orthogonal pure spectral resolution in a finite intrinsic algebra, with $\lambda_i\ge0$ and $\sum_i p_i=1$. Any included subalgebra $\mathcal X$ containing every $p_i$ preserves entropy, including the generated subalgebra. The spectral observable also preserves entropy. These are sufficient equality cases, not a characterization.
--
--   $$
--   H(\rho\mid_{\mathcal X})=H(\rho),\qquad H((\operatorname{Tr}\rho p_i)_i)=H(\rho).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 71, A.10-equality

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

/-- Equality cases following Theorem A.10, PDF p.71. Any subsystem containing
the full fine spectral resolution preserves entropy, as does its spectral observable. -/
theorem spectralEntropyEquality {A : IntrinsicSystem} {m : ℕ}
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : A.IsState rho)
    (p : Fin m → ℝ) (P : Fin m → Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hP : ∀ i, A.IsPureState (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (hcomplete : ∑ i, P i = 1)
    (hdecomp : rho = ∑ i, (p i : ℂ) • P i) :
    (∀ (X : IntrinsicSystem) (E : Embedding X A),
      (∀ i, ∃ T, InBlocks X.block T ∧ E.map T = P i) → viewedEntropy X E.map rho = vnEntropy rho) ∧
    countableEntropy (fun i => effectProb rho (P i)) = ENNReal.ofReal (vnEntropy rho) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_oneTester_realization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.oneTester_realization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:40:24.153991+00:00
-- url     : https://prove2.me/theorems/f12f6db7-8700-4bbb-a153-94dea4d588de
-- title:
--   Corollary 4 (Realization scheme for 1-testers)
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $\{P_i\}$ be a one-tester. There is an input density matrix $\sigma$ with $\sum_iP_i=I_{\rm out}\otimes\sigma$. Let $\Pi_\sigma$ be its support projection and choose arbitrary positive $Q_i$ summing to $I-I_{\rm out}\otimes\Pi_\sigma$. Define
--
--   $$
--   \widetilde P_i=(I\otimes\sqrt{\sigma^\ddagger})P_i(I\otimes\sqrt{\sigma^\ddagger})+Q_i.
--   $$
--
--   These operators form a POVM. For every channel $\mathcal C$ with Choi operator $C$, preparing $|\sqrt\sigma\rangle\rangle$, applying $\mathcal C\otimes\mathrm{id}$, and measuring the physical effects $\widetilde P_i^T$ yields $\operatorname{Re}\operatorname{Tr}(P_i^TC)$. The output state and every probability equality are included in the statement.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 18, Corollary 4 (Realization scheme for 1-testers)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.18, Corollary 4: preparation of |sqrt σ⟩⟩, one use of the channel, and a
transposed-POVM measurement reproduce the tester. The Q_i completion is arbitrary on
the kernel. The transposes in Eq.(70) are retained, correcting the preceding prose slip. -/
theorem oneTester_realization (s : Signature) (k : ℕ)
    (P : Fin k → Matrix (Basis s 1) (Basis s 1) ℂ)
    (hP : CombTester s 1 k P) :
    ∃ sigma : Matrix (Fin (s.input 0)) (Fin (s.input 0)) ℂ,
      IsDensityMatrix sigma ∧ (∑ i, P i) = oneInputLift s sigma ∧
      ∀ Q : Fin k → Matrix (Basis s 1) (Basis s 1) ℂ,
        (∀ i, (Q i).PosSemidef) →
        (∑ i, Q i) = 1 - oneInputLift s (QAlgorithms.Papers.Independent.Information100.P06.supportProjection sigma) →
        let E := fun i => oneInputLift s (matrixSqrt (pseudoInverse sigma)) * P i *
          oneInputLift s (matrixSqrt (pseudoInverse sigma)) + Q i
        POVM E ∧
        ∀ C : Matrix (Basis s 1) (Basis s 1) ℂ, Normalized s 1 C →
          IsDensityMatrix (onePurifiedOutput s C sigma) ∧
            ∀ i, QAlgorithms.effectProb (P i).transpose C = QAlgorithms.effectProb (E i).transpose (onePurifiedOutput s C sigma) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end

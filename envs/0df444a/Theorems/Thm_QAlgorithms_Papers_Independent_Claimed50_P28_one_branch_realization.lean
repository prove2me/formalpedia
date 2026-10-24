-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_one_branch_realization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.one_branch_realization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:28:16.150642+00:00
-- url     : https://prove2.me/theorems/11d70ced-14ee-43d3-8d8d-e3e7ac13221e
-- title:
--   Randomized von Neumann schemes for states and whole POVMs
-- statement:
--   For $d\ge1$ choose Haar $U\in SU(d)$ and perform the projective measurement $M_{U,k}=U^\dagger|k\rangle\langle k|U$. For each $U$ the effects are positive orthogonal projections and sum to $I$. With $D_{U,k}=(d+1)M_{U,k}-I$, every density matrix $\rho$ is reconstructed by
--
--   $$\rho=\int\sum_k\operatorname{Tr}(\rho M_{U,k})D_{U,k}\,dU.$$
--
--   For an unknown whole POVM $(E_j)_j$, retain every positive effect and the constraint $\sum_jE_j=I$. Choose the projective preparation label $k$ uniformly, prepare $M_{U,k}$, and observe the unknown POVM label $j$. Its joint probabilities are $p(k,j\mid U)=\operatorname{Tr}(E_jM_{U,k})/d$, are nonnegative, sum to one, and satisfy
--
--   $$E_j=d\int\sum_k p(k,j\mid U)D_{U,k}\,dU.$$
--
--   These are the one-branch implementations obtained by the stated one-dimensional input/output reductions. They keep the physical preparation normalization and do not identify a single effect with an entire unknown POVM. No ambiguous numerical optimum is asserted.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 4, Final paragraph: one-dimensional reductions

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF p.4, final paragraph: one-branch state and whole-POVM schemes are randomized
von Neumann measurements. All unknown POVM effects and their sum-to-I constraint are retained.
This implementation statement does not assert the paper's ambiguous numerical eta. -/
theorem one_branch_realization {d : ℕ} (hd : 0 < d)
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar) :
    (∀ U : SU d, (∀ k, (branchEffect U k).PosSemidef ∧
      branchEffect U k * branchEffect U k = branchEffect U k) ∧
      (∀ k l, k ≠ l → branchEffect U k * branchEffect U l = 0) ∧
      ∑ k, branchEffect U k = 1) ∧
    (∀ rho : Op (Fin d), QAlgorithms.IsDensityMatrix rho →
      (∫ U, ∑ k, (branchEffect U k * rho).trace • branchDual U k ∂haar) = rho) ∧
    (∀ (J : Type) [Fintype J] (E : J → Op (Fin d)),
      (∀ j, (E j).PosSemidef) → (∑ j, E j) = 1 →
      (∀ U k j, 0 ≤ branchPOVMProbability E U k j) ∧
      (∀ U, ∑ k, ∑ j, branchPOVMProbability E U k j = 1) ∧
      (∀ j, (∫ U, ∑ k, ((d : ℂ) * (branchPOVMProbability E U k j : ℂ)) •
        branchDual U k ∂haar) = E j)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end

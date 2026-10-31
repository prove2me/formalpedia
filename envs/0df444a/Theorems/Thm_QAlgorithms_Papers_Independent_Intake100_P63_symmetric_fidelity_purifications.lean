-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_symmetric_fidelity_purifications
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.symmetric_fidelity_purifications
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:20:27.533606+00:00
-- url     : https://prove2.me/theorems/bf81c62b-7876-47c5-a285-bf8ca56b75a6
-- title:
--   Lemma III.4: symmetric fidelity-attaining purifications
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space, $n\ge1$, $\rho\in\mathcal D(H)$, and $\rho_n\in\mathcal D(H^{\otimes n})$ invariant under conjugation by every copy permutation. Root fidelity is $F(A,B)=\operatorname{Tr}\sqrt{\sqrt A B\sqrt A}$. There are unit vectors $\theta\in H\otimes H$ and $\Psi_n\in(H\otimes H)^{\otimes n}$ such that
--   $$
--   \operatorname{Tr}_E|\theta\rangle\langle\theta|=\rho,\qquad
--   \operatorname{Tr}_{E^{\otimes n}}|\Psi_n\rangle\langle\Psi_n|=\rho_n,\qquad
--   |\langle\Psi_n\mid\theta^{\otimes n}\rangle|=F(\rho_n,\rho^{\otimes n}),
--   $$
--   and $\Psi_n$ is symmetric under permutations of the paired system-environment sites.
--
--   The original mixed state only needs permutation invariance, while the same purification witnesses meet both marginal and fidelity requirements.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 12, Lemma III.4: symmetric fidelity-attaining purifications

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.12 Lemma III.4: one pair of witnesses simultaneously purifies both
states and attains root fidelity; paired copies of the purification are symmetric. -/
theorem symmetric_fidelity_purifications {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (n : ℕ) (hn : 0 < n) (rho : Mat I) (hrho : IsDensityMatrix rho)
    (rhoN : Mat (Copies I n)) (hN : IsDensityMatrix rhoN)
    (hinvariant : ∀ p, permute p rhoN = rhoN) :
    ∃ theta : Vec (I × I), ∃ psi : Vec (Copies (I × I) n),
      IsState theta ∧ traceRight (pureDensity theta) = rho ∧ IsState psi ∧
      CopySymmetric psi ∧ discardEnvironment (pureDensity psi) = rhoN ∧
      ‖inner ℂ psi (tensorPow n theta)‖ = rootFidelity rhoN (piKron n rho) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end

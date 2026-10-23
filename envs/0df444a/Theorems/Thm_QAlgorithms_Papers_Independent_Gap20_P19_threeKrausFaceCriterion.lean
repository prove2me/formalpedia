-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_threeKrausFaceCriterion
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.threeKrausFaceCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:53:24.156446+00:00
-- url     : https://prove2.me/theorems/f2659bd4-d256-462b-a94c-8e421b93ba4c
-- title:
--   B.4: face antidegradability criterion (109)
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $\sigma_0=I$ and $\sigma_1,\sigma_2,\sigma_3=X,Y,Z$. For real amplitudes $a_k\ge0$ with $\sum_{k=0}^3a_k^2=1$, put $P_a(\rho)=\sum_{k=0}^3 a_k^2\sigma_k\rho\sigma_k$ and $\lambda_k=a_0^2+a_k^2-a_i^2-a_j^2$, where $\{i,j,k\}=\{1,2,3\}$.
--
--   Assume $a_0=0$ and $a_1,a_2,a_3\ne0$. Then
--   $$P_a\text{ is antidegradable}\iff(\lambda_i-\lambda_j)^2\le(1-3\lambda_k)(1+\lambda_k)$$
--   for every permutation $(i,j,k)$ of $(1,2,3)$. Swapping $a_0$ with any $a_n$ preserves antidegradability and supplies the corresponding criterion on the other three faces.
--
--   The source's nonzero face-interior hypotheses are kept; edges are treated separately.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 33, B.4: face antidegradability criterion (109)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

open Filter Topology

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
   maximumCoherentInformation dilationPower)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (MinimalDilation indexedKrausDilation arbitraryVectorComplement superopTensor tensorDilation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P69 (choi)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E F R K A2 B2 E2 : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype E] [DecidableEq E] [Nonempty E]

variable [Fintype F] [DecidableEq F] [Nonempty F]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype K] [DecidableEq K]

variable [Fintype A2] [DecidableEq A2] [Nonempty A2]

variable [Fintype B2] [DecidableEq B2] [Nonempty B2]

variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

/-- Appendix B.4, PDF pp.33–34, (109): interior of the a_0=0 face, with
nonzero remaining amplitudes. Other faces follow by swapping a_0 with a_n. -/
theorem threeKrausFaceCriterion (a : Fin 4 → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hnorm : ∑ k, a k^2 = 1)
    (hzero : a 0 = 0) (hpos : ∀ k : Fin 3, a k.succ ≠ 0) :
    ((∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (qubitPauliMap a) ∧ IsAntidegradable witness) ↔ ∀ k : Fin 3,
      (pauliMultipliers a (k+1)-pauliMultipliers a (k+2))^2 ≤
        (1-3*pauliMultipliers a k)*(1+pauliMultipliers a k)) ∧
    (∀ n : Fin 4, ∀ b : Fin 4 → ℝ,
      b = a ∘ Equiv.swap 0 n →
      ((∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (qubitPauliMap b) ∧ IsAntidegradable witness) ↔ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (qubitPauliMap a) ∧ IsAntidegradable witness))) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end

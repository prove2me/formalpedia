-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_common_optimal_srm
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.common_optimal_srm
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:28:33.804128+00:00
-- url     : https://prove2.me/theorems/d9b80f67-6c31-46d5-806d-b06f3cb9fa43
-- title:
--   The common SRM of three optimal qubit protocols
-- statement:
--   Let $N\ge1$ and $d=2$, with the physical singlet signals $\sigma_i$ and their sum $\rho$ as in Eqs.(4)-(5). Put $S_i=\rho^{-1/2}\sigma_i\rho^{-1/2}$ and $P_0=I-\operatorname{supp}\rho$, using support inverses. For the parity-correct physical spins $j$ of $N$ qubits, let $P_A(j)$ be their actual spectral projectors and $h_N(j)=\operatorname{tr}P_A(j)$. Define the normalized filters
--   $$O_{\mathrm{det}}=\sum_j\sqrt{\frac{2^{N+2}}{h_N(j)(N+2)}}\sin\frac{\pi(2j+1)}{N+2}\,P_A(j),$$
--   $$O_{\mathrm{prob}}=\sqrt{\frac{2^N}{\sum_j(2j+1)^2}}\sum_j\sqrt{\frac{(2j+1)^2}{h_N(j)}}P_A(j).$$
--   The completed effects $S_i+P_0/N$ form a deterministic POVM. They maximize entanglement fidelity with fixed $O=I$, and with $O_{\mathrm{det}}$ they attain the global maximum over normalized resources and deterministic POVMs. With $O_{\mathrm{prob}}$, the effects $S_i$ and the separate failure effect $P_0$ form an exact probabilistic PBT protocol attaining the global maximum success probability. Both lifted filters commute with $\rho$, and the support effects for $O_{\mathrm{det}}\sigma_iO_{\mathrm{det}}^\dagger$ are again $S_i$.
--
--   This is the coincidence of the physical measurements in the three cases, excluding fixed-resource probabilistic PBT. The Eq.(14) numerator is corrected from $2^{N+1}$ to $2^{N+2}$ using the source's intrinsic sector dimension.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 3, III Eqs.(12)-(15): common SRM in three optimal qubit protocols

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF p.3, Eqs.(12)-(15): the three optimal qubit protocols share SRM.
Each optimizer is constructed; optimality is a conclusion. The Eq.(14)
normalization is corrected to 2^(N+2) with intrinsic sector dimensions.
Fixed-resource probabilistic PBT is deliberately excluded. -/
theorem common_optimal_srm (N : ℕ) (hN : 1 ≤ N) :
    DeterministicPOVM (completedSRM 2 N) ∧
    (∀ E : Fin N → Op (AC 2 N), DeterministicPOVM E →
      pbtFidelity (1 : Op (Ports 2 N)) E ≤
        pbtFidelity (1 : Op (Ports 2 N)) (completedSRM 2 N)) ∧
    NormalizedResource (deterministicResource N) ∧
    (∀ (O : Op (Ports 2 N)) (E : Fin N → Op (AC 2 N)),
      NormalizedResource O → DeterministicPOVM E →
      pbtFidelity O E ≤ pbtFidelity (deterministicResource N) (completedSRM 2 N)) ∧
    ExactProbabilistic (probabilisticResource N) (probabilisticSRM 2 N) ∧
    (∀ (O : Op (Ports 2 N)) (E : Option (Fin N) → Op (AC 2 N)),
      ExactProbabilistic O E → pbtSuccessProbability O E ≤
        pbtSuccessProbability (probabilisticResource N) (probabilisticSRM 2 N)) ∧
    pbtRho 2 N * liftA (deterministicResource N) = liftA (deterministicResource N) * pbtRho 2 N ∧
    pbtRho 2 N * liftA (probabilisticResource N) = liftA (probabilisticResource N) * pbtRho 2 N ∧
    (∀ i, transformedSRM (deterministicResource N) i = srm 2 N i) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end

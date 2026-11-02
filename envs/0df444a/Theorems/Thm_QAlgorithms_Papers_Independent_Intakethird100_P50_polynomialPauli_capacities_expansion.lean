-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_polynomialPauli_capacities_expansion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.polynomialPauli_capacities_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:01:59.567292+00:00
-- url     : https://prove2.me/theorems/1a4067b7-697b-4138-9d17-da2d21f5ba8d
-- title:
--   Corollary 16: quantum/private bounds for polynomial Pauli noise
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces. A channel is complex-linear, completely positive and trace preserving. Its receiver and full complementary channel are obtained from the same isometric dilation. Write $Q(N)$ and $P(N)$ for the unassisted operational quantum and private capacities, allowing arbitrary collective codes over independent uses with vanishing reliability error and environmental leakage. Write $I_c(N)=\max_\rho[S(N(\rho))-S(N^c(\rho))]$, where the maximum includes every density operator. Entropies and logarithms are in bits, with $0\log 0=0$. The diamond norm has no factor $1/2$.
--
--   Let $p_1,p_2,p_3$ be real polynomials vanishing at zero, with $p_0(t)=1-\sum_i p_i(t)$ and physical four-component weights near $t=0$ from the right. Let $N_t$ be their qubit Pauli channel and $C=|c_1c_2+c_1c_3+c_2c_3|$, where $c_i$ is the linear coefficient of $p_i$. There exist $K_Q,K_P\ge0$ and $0<\delta\le1$, depending on the fixed family, such that for all $0<t<\delta$,
--   $$
--   I_c(N_t)\le Q(N_t)\le I_c(N_t)-512C t^2\log_2t+K_Qt^2,
--   $$
--   $$
--   I_c(N_t)\le P(N_t)\le I_c(N_t)-1536C t^2\log_2t+K_Pt^2.
--   $$
--   The case $C=0$ remains included. These estimates specialize the polynomial degradability expansion to quantum and private communication.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 17, Corollary 16: quantum/private bounds for polynomial Pauli noise

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P50

variable {A B E F : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel maximumCoherentInformation
    dilationPower idealJoint)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond choi)

open QAlgorithms.Papers.Independent.Support50.P07 (fullTracePrivateCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- Corollary 16, PDF p.17: the printed Q(N),P(N) denote the same N_p.
C_p=0 is included without using log C_p. -/
theorem polynomialPauli_capacities_expansion (P : Fin 3 → Polynomial ℝ)
    (hP : PolynomialNoise P) :
    ∃ Kq Kp : ℝ, 0 ≤ Kq ∧ 0 ≤ Kp ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ p ∈ Set.Ioo 0 delta,
        let V := pauliDilation (polynomialWeights P p)
        (maximumCoherentInformation V ≤ dilationQuantumCapacity V ∧
          dilationQuantumCapacity V ≤ maximumCoherentInformation V -
            512 * pairCoefficient P * p ^ 2 * log2 p + Kq * p ^ 2) ∧
        (maximumCoherentInformation V ≤ fullTracePrivateCapacity V ∧
          fullTracePrivateCapacity V ≤ maximumCoherentInformation V -
            1536 * pairCoefficient P * p ^ 2 * log2 p + Kp * p ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end

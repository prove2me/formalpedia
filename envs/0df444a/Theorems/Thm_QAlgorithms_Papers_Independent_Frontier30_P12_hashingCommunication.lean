-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P12_hashingCommunication
-- name    : QAlgorithms.Papers.Independent.Frontier30.P12.hashingCommunication
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:11:04.30019+00:00
-- url     : https://prove2.me/theorems/fc953d50-cd9b-4724-88aa-82b511d2e95b
-- title:
--   Remark 11: communication cost of the hashing construction
-- statement:
--   Let $|\psi\rangle^{ABE}$ be a unit vector on finite complex registers of positive dimension, put $\rho^{AB}=\operatorname{Tr}_E|\psi\rangle\langle\psi|$, and suppose $I_c(A\rangle B)_\rho>0$. There is one sequence of finite one-way EPR distillation protocols on $\rho^{\otimes n}$ with squared EPR fidelity tending to one, such that
--
--   $$\lim_{n\to\infty}\frac{\log_2M_n}{n}=I_c(A\rangle B)_\rho,\qquad\lim_{n\to\infty}\frac{\log_2L_n}{n}=I(A:E)_\psi=H(A)_\psi-H(B)_\psi+H(E)_\psi.$$
--
--   Here $M_n$ is the EPR Schmidt rank and $L_n$ is the public message alphabet size of that same protocol; entropies are in bits. Purity also gives $H(AE)=H(B)$, so the displayed cost equals $H(A)+H(E)-H(AE)$.
--
--   This is the communication attained by the hashing construction, combining code and Fourier measurement information. It is not a minimum-communication theorem.
-- source:
--   Distillation of secret key and entanglement from quantum states, arXiv:quant-ph/0306078v1, PDF p. 8, Remark 11

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- arXiv:quant-ph/0306078v1, PDF p.8, Remark 11. A normalized purification
specifies the environment, and the conclusion gives an attained rate/cost pair
for the construction, with no assertion of minimum communication. -/
theorem hashingCommunication {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    [Nonempty A] [Nonempty B] [Nonempty E]
    (psi : Vec (A × (B × E))) (hpsi : ‖psi‖ = 1)
    (hpos : 0 < coherentInfo (marginalAB (QAlgorithms.pureDensity psi))) :
    (∃ P : (n : ℕ) → EntProtocol A B n,
      EntAchieves (marginalAB (QAlgorithms.pureDensity psi)) P
        (coherentInfo (marginalAB (QAlgorithms.pureDensity psi))) ∧
      Tendsto (fun n => Real.logb 2 ((P n).alice.l : ℝ) / n) atTop
        (nhds (mutualAE (QAlgorithms.pureDensity psi)))) ∧
    mutualAE (QAlgorithms.pureDensity psi) =
      QAlgorithms.vnEntropy (QAlgorithms.traceRight (QAlgorithms.pureDensity psi)) -
      QAlgorithms.vnEntropy (QAlgorithms.traceRight
        (QAlgorithms.traceLeft (QAlgorithms.pureDensity psi))) +
      QAlgorithms.vnEntropy (QAlgorithms.traceLeft
        (QAlgorithms.traceLeft (QAlgorithms.pureDensity psi))) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P12

end

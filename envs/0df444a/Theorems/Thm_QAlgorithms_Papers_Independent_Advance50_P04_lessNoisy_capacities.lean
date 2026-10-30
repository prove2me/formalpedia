-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P04_lessNoisy_capacities
-- name    : QAlgorithms.Papers.Independent.Advance50.P04.lessNoisy_capacities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:20:06.573041+00:00
-- url     : https://prove2.me/theorems/1d25c169-8314-4e84-b22d-888685c24bce
-- title:
--   Theorem 2: less noisy channels have single-letter capacities
-- statement:
--   Let $a,b,e\ge1$ and let $U:\mathbb C^a\to\mathbb C^b\otimes\mathbb C^e$ be an isometry. Define the channel and its complement by $N_B(\rho)=\operatorname{Tr}_E(U\rho U^*)$ and $N_E(\rho)=\operatorname{Tr}_B(U\rho U^*)$. All input states are positive semidefinite trace-one matrices, and all entropies use base-two logarithms.
--
--   Write $I_c(\rho)=H(N_B(\rho))-H(N_E(\rho))$, $Q^{(1)}(N_B)=\max_\rho I_c(\rho)$, and $C_p^{(1)}(N_B)=\max[I(L;B)-I(L;E)]$, where the last maximum ranges over every finite ensemble of mixed input states and uses that same ensemble for both outputs. Here $I$ is Holevo information. The unassisted capacities $Q$ and $C_p$ are the limits of the corresponding optimized $n$-use quantities divided by $n$, over positive block lengths; joint inputs may be entangled across uses. A channel is less noisy when $C_p(N_E)=0$. For every such channel,
--
--   $$C_p(N_B)=Q(N_B)=Q^{(1)}(N_B).$$
--
--   Thus no regularization is needed to compute either capacity in this class; the one-use maximum still permits mixed input states.
-- source:
--   Private and Quantum Capacities of More Capable and Less Noisy Quantum Channels, arXiv:1110.5746v3, PDF p. 3, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P04

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel dilationPower
    maximumCoherentInformation IsDegradable)

open QAlgorithms.Papers.Independent.Support50.P01 (ConjugateDegradable)

open QAlgorithms.Papers.Independent.Information100.P56 (average)

open QAlgorithms.Papers.Independent.Dependency50.P48
  (holevoInformation privateMaximum regularizedCoherentInformation)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B E : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E]

variable {a b e : ℕ}

/-- Theorem 2, PDF p.3; proof Section IV.C, p.6: both equalities, with the
ordinary unrestricted one-use mixed-input coherent-information maximum. -/
theorem lessNoisy_capacities (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : IsIsometry U)
    (h : LessNoisy U) : (Filter.limUnder Filter.atTop (fun n : ℕ =>
      privateMaximum (dilationPower U (n + 1)) / ((n + 1 : ℕ) : ℝ))) = regularizedCoherentInformation U ∧
      regularizedCoherentInformation U = maximumCoherentInformation U := by sorry

end QAlgorithms.Papers.Independent.Advance50.P04

end

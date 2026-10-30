-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P04_degradable_lessNoisy
-- name    : QAlgorithms.Papers.Independent.Advance50.P04.degradable_lessNoisy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:28:15.254726+00:00
-- url     : https://prove2.me/theorems/320b4958-ca00-4b45-a248-475c34ab0d78
-- title:
--   Unnumbered: degradable channels lie in the less noisy class (Fig.1)
-- statement:
--   Let $a,b,e\ge1$ and let $U:\mathbb C^a\to\mathbb C^b\otimes\mathbb C^e$ be an isometry. Define the channel and its complement by $N_B(\rho)=\operatorname{Tr}_E(U\rho U^*)$ and $N_E(\rho)=\operatorname{Tr}_B(U\rho U^*)$. All input states are positive semidefinite trace-one matrices, and all entropies use base-two logarithms.
--
--   Write $I_c(\rho)=H(N_B(\rho))-H(N_E(\rho))$, $Q^{(1)}(N_B)=\max_\rho I_c(\rho)$, and $C_p^{(1)}(N_B)=\max[I(L;B)-I(L;E)]$, where the last maximum ranges over every finite ensemble of mixed input states and uses that same ensemble for both outputs. Here $I$ is Holevo information. The unassisted capacities $Q$ and $C_p$ are the limits of the corresponding optimized $n$-use quantities divided by $n$, over positive block lengths; joint inputs may be entangled across uses. Suppose a single completely positive trace-preserving map $\mathcal D:B\to E$ satisfies $\mathcal D\circ N_B=N_E$ on every input operator. Then
--
--   $$N_B\text{ is less noisy},\quad\text{that is, }C_p(N_E)=0.$$
--
--   This is the degradable branch of Figure 1. No strictness of this inclusion is asserted.
-- source:
--   Private and Quantum Capacities of More Capable and Less Noisy Quantum Channels, arXiv:1110.5746v3, PDF p. 2, Figure 1; Section II

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

/-- Figure 1, PDF p.2, with the degrading-map definition in Section II, pp.2–3:
ordinary degradable channels belong to the less noisy class. -/
theorem degradable_lessNoisy (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (h : IsDegradable U) :
    LessNoisy U := by sorry

end QAlgorithms.Papers.Independent.Advance50.P04

end

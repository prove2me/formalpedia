-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P04_lessNoisy_iff_mixedDominance
-- name    : QAlgorithms.Papers.Independent.Advance50.P04.lessNoisy_iff_mixedDominance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:25:31.649985+00:00
-- url     : https://prove2.me/theorems/6c1df445-57bb-4c96-8cec-514ee86d5d00
-- title:
--   Unnumbered: Eq.(7) characterizes less noisiness
-- statement:
--   Let $a,b,e\ge1$ and let $U:\mathbb C^a\to\mathbb C^b\otimes\mathbb C^e$ be an isometry. Define the channel and its complement by $N_B(\rho)=\operatorname{Tr}_E(U\rho U^*)$ and $N_E(\rho)=\operatorname{Tr}_B(U\rho U^*)$. All input states are positive semidefinite trace-one matrices, and all entropies use base-two logarithms.
--
--   Write $I_c(\rho)=H(N_B(\rho))-H(N_E(\rho))$, $Q^{(1)}(N_B)=\max_\rho I_c(\rho)$, and $C_p^{(1)}(N_B)=\max[I(L;B)-I(L;E)]$, where the last maximum ranges over every finite ensemble of mixed input states and uses that same ensemble for both outputs. Here $I$ is Holevo information. The unassisted capacities $Q$ and $C_p$ are the limits of the corresponding optimized $n$-use quantities divided by $n$, over positive block lengths; joint inputs may be entangled across uses. Less noisiness means $C_p(N_E)=0$. For each positive integer $n$, take any finite ensemble of mixed states on $(\mathbb C^a)^{\otimes n}$ and let $L$ be its classical label. Then
--
--   $$N_B\text{ is less noisy}\quad\Longleftrightarrow\quad I(L;B^n)\ge I(L;E^n)\quad\text{for every }n\ge1\text{ and every such ensemble}. $$
--
--   The finite label alphabet is unrestricted, and neither states nor probabilities are constrained to product form. This identifies the all-block meaning of the less noisy condition.
-- source:
--   Private and Quantum Capacities of More Capable and Less Noisy Quantum Channels, arXiv:1110.5746v3, PDF p. 3, Section III, Eq. (7)

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

/-- Section III, PDF p.3, Eq.(7): mixed ensembles of arbitrary finite cardinality
on the whole input tensor space, at every positive block length. -/
theorem lessNoisy_iff_mixedDominance (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : IsIsometry U) :
    LessNoisy U ↔ ∀ n : ℕ, 0 < n → MixedDominance (dilationPower U n) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P04

end

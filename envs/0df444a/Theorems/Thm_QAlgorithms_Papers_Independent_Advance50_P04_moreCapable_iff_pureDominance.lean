-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P04_moreCapable_iff_pureDominance
-- name    : QAlgorithms.Papers.Independent.Advance50.P04.moreCapable_iff_pureDominance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:24:33.942991+00:00
-- url     : https://prove2.me/theorems/27acedbf-5fbb-45bd-b2c5-9cc74f44cee8
-- title:
--   Unnumbered: Eq.(6) characterizes more capability
-- statement:
--   Let $a,b,e\ge1$ and let $U:\mathbb C^a\to\mathbb C^b\otimes\mathbb C^e$ be an isometry. Define the channel and its complement by $N_B(\rho)=\operatorname{Tr}_E(U\rho U^*)$ and $N_E(\rho)=\operatorname{Tr}_B(U\rho U^*)$. All input states are positive semidefinite trace-one matrices, and all entropies use base-two logarithms.
--
--   Write $I_c(\rho)=H(N_B(\rho))-H(N_E(\rho))$, $Q^{(1)}(N_B)=\max_\rho I_c(\rho)$, and $C_p^{(1)}(N_B)=\max[I(L;B)-I(L;E)]$, where the last maximum ranges over every finite ensemble of mixed input states and uses that same ensemble for both outputs. Here $I$ is Holevo information. The unassisted capacities $Q$ and $C_p$ are the limits of the corresponding optimized $n$-use quantities divided by $n$, over positive block lengths; joint inputs may be entangled across uses. More capability means $Q(N_E)=0$. For each positive integer $n$, let $X$ label $a^n$ arbitrary unit vectors on $(\mathbb C^a)^{\otimes n}$ with an arbitrary joint probability distribution. Then
--
--   $$N_B\text{ is more capable}\quad\Longleftrightarrow\quad I(X;B^n)\ge I(X;E^n)\quad\text{for every }n\ge1\text{ and every such pure ensemble}. $$
--
--   The vectors may be entangled across channel uses; neither the prior nor the inputs need be products. This characterizes the capacity-defined class by its all-block pure-ensemble inequalities.
-- source:
--   Private and Quantum Capacities of More Capable and Less Noisy Quantum Channels, arXiv:1110.5746v3, PDF p. 3, Section III, Eq. (6)

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

/-- Section III, PDF p.3, Eq.(6): all positive block lengths, arbitrary joint
pure inputs and arbitrary joint probability laws of length a^n. -/
theorem moreCapable_iff_pureDominance (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : IsIsometry U) :
    MoreCapable U ↔ ∀ n : ℕ, 0 < n → PureDominance (dilationPower U n) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P04

end

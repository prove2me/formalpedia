-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P04_mixedDominance_iff_concavity
-- name    : QAlgorithms.Papers.Independent.Advance50.P04.mixedDominance_iff_concavity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:22:24.996824+00:00
-- url     : https://prove2.me/theorems/1c6e587b-dc6e-4dd2-ae2d-645e4248d452
-- title:
--   Proposition 3: mixed-ensemble dominance iff coherent-information concavity
-- statement:
--   Let $a,b,e\ge1$ and let $U:\mathbb C^a\to\mathbb C^b\otimes\mathbb C^e$ be an isometry. Define the channel and its complement by $N_B(\rho)=\operatorname{Tr}_E(U\rho U^*)$ and $N_E(\rho)=\operatorname{Tr}_B(U\rho U^*)$. All input states are positive semidefinite trace-one matrices, and all entropies use base-two logarithms.
--
--   Write $\mathcal M(N_B)$ for one-use mixed-ensemble dominance: for every finite ensemble $\{p_i,\rho_i\}$ of normalized mixed input states, with $p_i\ge0$ and $\sum_i p_i=1$, the Holevo informations satisfy $I(L;B)\ge I(L;E)$. Define $I_c(\rho)=H(N_B(\rho))-H(N_E(\rho))$. Then
--
--   $$\mathcal M(N_B)\quad\Longleftrightarrow\quad I_c\!\left(\sum_{i=1}^m p_i\rho_i\right)\ge\sum_{i=1}^m p_i I_c(\rho_i)\quad\text{for every finite input ensemble}. $$
--
--   The averaged state is constructed from the ensemble, including zero weights. This is concavity on the entire density-matrix set, not the all-block less noisy condition.
-- source:
--   Private and Quantum Capacities of More Capable and Less Noisy Quantum Channels, arXiv:1110.5746v3, PDF p. 5, Proposition 3

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

/-- Proposition 3, PDF p.5: one-use mixed-ensemble dominance iff coherent
information is concave on all finite mixtures of normalized input states. -/
theorem mixedDominance_iff_concavity (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : IsIsometry U) :
    MixedDominance U ↔ CoherentConcave U := by sorry

end QAlgorithms.Papers.Independent.Advance50.P04

end

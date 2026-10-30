-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P04_mixedDominance_iff_divergence
-- name    : QAlgorithms.Papers.Independent.Advance50.P04.mixedDominance_iff_divergence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:23:34.933268+00:00
-- url     : https://prove2.me/theorems/0bfe21e1-4094-48d5-9056-fade2ba106a3
-- title:
--   Proposition 4: one-use mixed dominance iff divergence dominance
-- statement:
--   Let $a,b,e\ge1$ and let $U:\mathbb C^a\to\mathbb C^b\otimes\mathbb C^e$ be an isometry. Define the channel and its complement by $N_B(\rho)=\operatorname{Tr}_E(U\rho U^*)$ and $N_E(\rho)=\operatorname{Tr}_B(U\rho U^*)$. All input states are positive semidefinite trace-one matrices, and all entropies use base-two logarithms.
--
--   Write $\mathcal M(N_B)$ for one-use mixed-ensemble dominance: for every finite ensemble $\{p_i,\rho_i\}$ of normalized mixed input states, with $p_i\ge0$ and $\sum_i p_i=1$, the Holevo informations satisfy $I(L;B)\ge I(L;E)$. Let $D(\rho\Vert\sigma)$ be the extended Umegaki relative entropy: it equals $+\infty$ if the support of $\rho$ is not contained in the support of $\sigma$. Then
--
--   $$\mathcal M(N_B)\quad\Longleftrightarrow\quad D(N_B(\rho)\Vert N_B(\sigma))\ge D(N_E(\rho)\Vert N_E(\sigma))\quad\text{for all input states }\rho,\sigma.$$
--
--   This equivalence concerns one use and includes singular states and infinite divergences. A common positive conversion from natural logs to bits leaves the comparison unchanged.
-- source:
--   Private and Quantum Capacities of More Capable and Less Noisy Quantum Channels, arXiv:1110.5746v3, PDF p. 5, Proposition 4

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

/-- Proposition 4, PDF p.5: one-use Eq.(7) iff one-use Eq.(8).
Extended nonnegative relative entropies include support violations. -/
theorem mixedDominance_iff_divergence (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : IsIsometry U) :
    MixedDominance U ↔ DivergenceDominance U := by sorry

end QAlgorithms.Papers.Independent.Advance50.P04

end

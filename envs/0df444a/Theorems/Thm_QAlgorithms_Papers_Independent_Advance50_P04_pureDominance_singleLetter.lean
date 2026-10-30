-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P04_pureDominance_singleLetter
-- name    : QAlgorithms.Papers.Independent.Advance50.P04.pureDominance_singleLetter
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:20:53.523564+00:00
-- url     : https://prove2.me/theorems/50d1d1a1-3d22-4862-a016-63c2724b44e1
-- title:
--   Proposition 1: one-use pure-ensemble dominance suffices
-- statement:
--   Let $a,b,e\ge1$ and let $U:\mathbb C^a\to\mathbb C^b\otimes\mathbb C^e$ be an isometry. Define the channel and its complement by $N_B(\rho)=\operatorname{Tr}_E(U\rho U^*)$ and $N_E(\rho)=\operatorname{Tr}_B(U\rho U^*)$. All input states are positive semidefinite trace-one matrices, and all entropies use base-two logarithms.
--
--   Write $I_c(\rho)=H(N_B(\rho))-H(N_E(\rho))$, $Q^{(1)}(N_B)=\max_\rho I_c(\rho)$, and $C_p^{(1)}(N_B)=\max[I(L;B)-I(L;E)]$, where the last maximum ranges over every finite ensemble of mixed input states and uses that same ensemble for both outputs. Here $I$ is Holevo information. The unassisted capacities $Q$ and $C_p$ are the limits of the corresponding optimized $n$-use quantities divided by $n$, over positive block lengths; joint inputs may be entangled across uses.
--
--   Write $\mathcal P(N_B)$ for the following one-use condition: for every probability vector $(p_x)_{x=1}^a$ and every family of unit input vectors $(\psi_x)_{x=1}^a$, the pure ensemble satisfies $I(X;B)\ge I(X;E)$. The probabilities may vanish and the vectors need not be orthogonal. Then
--
--   $$\mathcal P(N_B)\ \Longrightarrow\ C_p^{(1)}(N_B)=Q^{(1)}(N_B).$$
--
--   This is a one-use statement and does not assume the all-block more capable condition.
-- source:
--   Private and Quantum Capacities of More Capable and Less Noisy Quantum Channels, arXiv:1110.5746v3, PDF p. 4, Proposition 1

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

/-- Proposition 1, PDF p.4: the premise is Eq.(6) for n=1 alone. -/
theorem pureDominance_singleLetter (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : IsIsometry U)
    (h : PureDominance U) : privateMaximum U = maximumCoherentInformation U := by sorry

end QAlgorithms.Papers.Independent.Advance50.P04

end

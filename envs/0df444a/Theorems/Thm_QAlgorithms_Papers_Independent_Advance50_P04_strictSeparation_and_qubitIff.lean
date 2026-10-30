-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P04_strictSeparation_and_qubitIff
-- name    : QAlgorithms.Papers.Independent.Advance50.P04.strictSeparation_and_qubitIff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:21:38.644553+00:00
-- url     : https://prove2.me/theorems/c5a81e9e-e636-4dcf-be51-a3b54cb84363
-- title:
--   Proposition 2: strict separation and the qubit iff
-- statement:
--   Let $a,b,e\ge1$ and let $U:\mathbb C^a\to\mathbb C^b\otimes\mathbb C^e$ be an isometry. Define the channel and its complement by $N_B(\rho)=\operatorname{Tr}_E(U\rho U^*)$ and $N_E(\rho)=\operatorname{Tr}_B(U\rho U^*)$. All input states are positive semidefinite trace-one matrices, and all entropies use base-two logarithms.
--
--   Write $I_c(\rho)=H(N_B(\rho))-H(N_E(\rho))$, $Q^{(1)}(N_B)=\max_\rho I_c(\rho)$, and $C_p^{(1)}(N_B)=\max[I(L;B)-I(L;E)]$, where the last maximum ranges over every finite ensemble of mixed input states and uses that same ensemble for both outputs. Here $I$ is Holevo information. The unassisted capacities $Q$ and $C_p$ are the limits of the corresponding optimized $n$-use quantities divided by $n$, over positive block lengths; joint inputs may be entangled across uses.
--
--   Write $\mathcal P(N_B)$ for the following one-use condition: for every probability vector $(p_x)_{x=1}^a$ and every family of unit input vectors $(\psi_x)_{x=1}^a$, the pure ensemble satisfies $I(X;B)\ge I(X;E)$. The probabilities may vanish and the vectors need not be orthogonal. The following are separate assertions.
--
--   1. If $\mathcal P(N_B)$ fails and there exists a full-rank density matrix $\rho_*$ globally maximizing $I_c$, then
--
--   $$C_p^{(1)}(N_B)>Q^{(1)}(N_B).$$
--
--   2. If $a=2$ and $C_p^{(1)}(N_B)>0$, then
--
--   $$C_p^{(1)}(N_B)=Q^{(1)}(N_B)\quad\Longleftrightarrow\quad\mathcal P(N_B).$$
--
--   Only existence of one full-rank maximizer is required in the first assertion. The second assertion has neither of the first assertion's premises. This separates the general sufficient condition from its qubit necessity.
-- source:
--   Private and Quantum Capacities of More Capable and Less Noisy Quantum Channels, arXiv:1110.5746v3, PDF p. 4, Proposition 2

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

/-- Proposition 2, PDF pp.4–5: one full-rank global maximizer suffices for the
first clause; the qubit iff has only its own dimension and positivity premises. -/
theorem strictSeparation_and_qubitIff (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : IsIsometry U) :
    (¬ PureDominance U →
      (∃ rho : Matrix (Fin a) (Fin a) ℂ, IsDensityMatrix rho ∧ rho.PosDef ∧
        ∀ sigma : Matrix (Fin a) (Fin a) ℂ, IsDensityMatrix sigma →
          coherentValue U sigma ≤ coherentValue U rho) →
      maximumCoherentInformation U < privateMaximum U) ∧
    (a = 2 → 0 < privateMaximum U →
      (privateMaximum U = maximumCoherentInformation U ↔ PureDominance U)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P04

end

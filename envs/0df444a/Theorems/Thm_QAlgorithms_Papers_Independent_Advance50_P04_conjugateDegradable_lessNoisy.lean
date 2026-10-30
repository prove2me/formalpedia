-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P04_conjugateDegradable_lessNoisy
-- name    : QAlgorithms.Papers.Independent.Advance50.P04.conjugateDegradable_lessNoisy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:27:38.724007+00:00
-- url     : https://prove2.me/theorems/ce597d54-1806-475f-aba7-b1100e70f8f7
-- title:
--   Unnumbered: conjugate degradable channels are less noisy
-- statement:
--   Let $a,b,e\ge1$ and let $U:\mathbb C^a\to\mathbb C^b\otimes\mathbb C^e$ be an isometry. Define the channel and its complement by $N_B(\rho)=\operatorname{Tr}_E(U\rho U^*)$ and $N_E(\rho)=\operatorname{Tr}_B(U\rho U^*)$. All input states are positive semidefinite trace-one matrices, and all entropies use base-two logarithms.
--
--   Write $I_c(\rho)=H(N_B(\rho))-H(N_E(\rho))$, $Q^{(1)}(N_B)=\max_\rho I_c(\rho)$, and $C_p^{(1)}(N_B)=\max[I(L;B)-I(L;E)]$, where the last maximum ranges over every finite ensemble of mixed input states and uses that same ensemble for both outputs. Here $I$ is Holevo information. The unassisted capacities $Q$ and $C_p$ are the limits of the corresponding optimized $n$-use quantities divided by $n$, over positive block lengths; joint inputs may be entangled across uses. Suppose a single completely positive trace-preserving map $\mathcal D:B\to E$ satisfies $\mathcal D(N_B(\rho))=\overline{N_E(\rho)}$ for every density matrix, where conjugation uses a fixed environment basis. Then
--
--   $$C_p(N_E)=0,\qquad N_B\text{ is less noisy},\qquad C_p(N_B)=Q(N_B)=Q^{(1)}(N_B).$$
--
--   The same map works for all inputs. In the complex-linear extension to all operators, conjugation of a Hermitian state is represented by transpose. This places conjugate degradable channels in the less noisy class and retains the announced private-capacity equality.
-- source:
--   Private and Quantum Capacities of More Capable and Less Noisy Quantum Channels, arXiv:1110.5746v3, PDF p. 3, Sections II–III, conjugate degradable channels

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

/-- Section III, PDF p.3: conjugate degradability gives zero private capacity
to the complement, hence less noisiness; retain the capacity chain announced
in Section II, p.3. Transpose is conjugation on Hermitian density matrices. -/
theorem conjugateDegradable_lessNoisy (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (h : ConjugateDegradable U) :
    (Filter.limUnder Filter.atTop (fun n : ℕ =>
      privateMaximum (dilationPower (swapDilation U) (n + 1)) / ((n + 1 : ℕ) : ℝ))) = 0 ∧ LessNoisy U ∧
      (Filter.limUnder Filter.atTop (fun n : ℕ =>
      privateMaximum (dilationPower U (n + 1)) / ((n + 1 : ℕ) : ℝ))) = regularizedCoherentInformation U ∧
      regularizedCoherentInformation U = maximumCoherentInformation U := by sorry

end QAlgorithms.Papers.Independent.Advance50.P04

end

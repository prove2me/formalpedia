-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_probabilistic_characterization
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.probabilistic_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:25:31.257557+00:00
-- url     : https://prove2.me/theorems/2a1a1e81-a785-4467-b5c8-74981d1095ab
-- title:
--   Faithful protocols are exactly the success SDP
-- statement:
--   Fix $N\ge1$. Let $O$ be any square resource operator with $\operatorname{tr}(O^\dagger O)=2^N$, and let $\Pi_i\ge0$ be input-independent successful effects satisfying $\sum_i\Pi_i\le I$; the remaining positive effect denotes failure. Set $X=O^\dagger O$ and $\widetilde\Pi_i=(O^\dagger\otimes I)\Pi_i(O\otimes I)$. A protocol returns every normalized unknown pure qubit exactly on each successful branch if and only if there exist positive operators $\Theta_i$ on the $N-1$ unused Alice qubits such that
--
--   $$\widetilde\Pi_i=P^-_{A_iC}\otimes\Theta_i,\qquad\sum_i P^-_{A_iC}\otimes\Theta_i\le X\otimes I.$$
--
--   Its Haar average success probability is
--
--   $$p=2^{-(N+1)}\sum_i\operatorname{tr}\Theta_i.$$
--
--   Conversely, every positive $X$ of trace $2^N$ and positive family $\Theta_i$ satisfying this inequality is realized by a physical faithful sub-POVM with resource operator $\sqrt X$, the stated transformed effects, and this success probability. This includes singular $X$.
--
--   Thus the success SDP represents all physical protocols in the stated model, rather than imposing its factorization as an assumption.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 7, §V, Eqs. (43)–(47)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF p.7, Eqs.(43)–(47): faithfulness is characterized, not assumed, by the singlet
factorization of transformed successful effects. Every feasible SDP point is physically
realizable, even for singular X; the positive remainder is the failure outcome. -/
theorem probabilistic_characterization (N : ℕ) (hN : 1 ≤ N) :
    (∀ (O : Matrix (Qubits N) (Qubits N) ℂ)
      (M : Fin N → Matrix (AC N) (AC N) ℂ), SubPOVM O M →
      (IsFaithfulPortProtocol O M ↔ ∃ T : (i : Fin N) →
        Matrix (Other N i → Bool) (Other N i → Bool) ℂ,
        PortSuccessFeasible N (Oᴴ * O) T ∧
        (∀ i, transformed O (M i) = embedTheta i (T i)) ∧
        portSuccessProbability O M = successObjective T)) ∧
    (∀ (X : Matrix (Qubits N) (Qubits N) ℂ)
      (T : (i : Fin N) → Matrix (Other N i → Bool) (Other N i → Bool) ℂ),
      PortSuccessFeasible N X T → ∃ M : Fin N → Matrix (AC N) (AC N) ℂ,
        IsProbabilisticPortProtocol (resourceOperator X) M ∧
        (∀ i, transformed (resourceOperator X) (M i) = embedTheta i (T i)) ∧
        portSuccessProbability (resourceOperator X) M = successObjective T) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end

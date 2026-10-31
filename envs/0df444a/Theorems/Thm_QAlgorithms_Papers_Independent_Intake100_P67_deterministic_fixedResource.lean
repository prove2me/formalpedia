-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_deterministic_fixedResource
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.deterministic_fixedResource
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:20:58.330517+00:00
-- url     : https://prove2.me/theorems/588a3ed3-9138-4e7c-8618-c4b537332f44
-- title:
--   Fixed singlet resource: completed SRM and exact fidelity
-- statement:
--   Let $N\ge1$, fix the resource to $|\psi^-\rangle^{\otimes N}$, and retain the input-independent, correction-free protocol model above. Put $\sigma_i=2^{-(N-1)}P^-_{A_iC}\otimes I_{\bar A_i}$ and $\rho=\sum_i\sigma_i$. Inverse powers are taken on the support. The effects
--
--   $$\Pi_i=\rho^{-1/2}\sigma_i\rho^{-1/2}+\frac1N\left(I-\sum_j\rho^{-1/2}\sigma_j\rho^{-1/2}\right)$$
--
--   form a POVM and attain the largest possible entanglement fidelity for this resource, namely
--
--   $$F_{\rm ME}(N)=\frac1{2^{N+3}}\sum_{k=0}^N\binom Nk\left(\frac{N-2k-1}{\sqrt{k+1}}+\frac{N-2k+1}{\sqrt{N-k+1}}\right)^2.$$
--
--   The corresponding Haar average is $(2F_{\rm ME}+1)/3$, and it exceeds $2/3$ whenever $N\ge3$.
--
--   The evaluation is the present paper's result; the paper attributes optimality of the SRM to reference [25].
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 5, §IV A, Eqs. (27)–(30)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF p.5, Eqs.(27)–(30): completed SRM is optimal for the fixed singlet resource.
The source credits SRM optimality to [25]; this paper evaluates Eq.(29). -/
theorem deterministic_fixedResource (N : ℕ) (hN : 1 ≤ N) :
    IsDeterministicPortProtocol (1 : Matrix (Qubits N) (Qubits N) ℂ) (completedSRM (portSignal N)) ∧
    entFidelity (1 : Matrix (Qubits N) (Qubits N) ℂ) (completedSRM (portSignal N)) =
      fixedFidelity N ∧
    (∀ M : Fin N → Matrix (AC N) (AC N) ℂ,
      IsDeterministicPortProtocol (1 : Matrix (Qubits N) (Qubits N) ℂ) M →
        entFidelity (1 : Matrix (Qubits N) (Qubits N) ℂ) M ≤ fixedFidelity N) ∧
    (3 ≤ N → (2 * fixedFidelity N + 1) / 3 > 2 / 3) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end

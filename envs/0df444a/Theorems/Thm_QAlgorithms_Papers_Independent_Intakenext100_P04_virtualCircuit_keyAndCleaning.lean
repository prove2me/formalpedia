-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P04_virtualCircuit_keyAndCleaning
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P04.virtualCircuit_keyAndCleaning
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:49:26.295474+00:00
-- url     : https://prove2.me/theorems/666bb3d4-1527-458b-81fc-804adb6ace6f
-- title:
--   The virtual circuit computes the same key and cleans its ancilla
-- statement:
--   Let $N>0$, and let $G:\mathbb F_2^r\to\mathbb F_2^N$ be an injective linear encoder with decoder $f$ and correctable set $\mathcal E$, meaning $f(G(y)+x)=y$ for all $y$ and all $x\in\mathcal E$. Form the actual Z-basis permutation unitaries
--
--   $$
--   U_1|x,y\rangle_Z=|x+G(y),y\rangle_Z,\qquad U_2|x,y\rangle_Z=|x,y+f(x)\rangle_Z,\qquad U=U_2U_1.
--   $$
--
--   Append $|0\rangle_X$ on $Q$. The Heisenberg effect of measuring $Q$ in the X basis with output $y$ after $U$ equals the effect of directly measuring $S$ in the X basis and applying $G^T$. Consequently the key channel, including its joint law with Eve, is the same. On each correctable basis state,
--
--   $$
--   U(|x\rangle_Z\otimes|0\rangle_X)=2^{-r/2}\sum_y|x+G(y)\rangle_Z\otimes|0\rangle_Z\quad(x\in\mathcal E).
--   $$
--
--   For any positive trace-one joint state $\rho_{SE}$ with arbitrary Eve dimension, put $P=P_{\mathcal E}\otimes I_E$ and $q=\operatorname{Tr}(P\rho_{SE})$. The actual ancilla marginal satisfies
--
--   $$
--   \langle0|\rho_Q|0\rangle_Z\ge q.
--   $$
--
--   If $q>0$, the constructed normalized projected state $\rho'=P\rho_{SE}P/q$ is positive trace class and its squared fidelity with $\rho_{SE}$ equals $q$. If $q=1$, then $\rho_Q=|0\rangle_Z\langle0|$ and every Eve measurement has joint key law $\Pr(Y=y,Z=z)=2^{-r}\Pr(Z=z)$. This is the circuit-level decoupling mechanism; no probability of protocol acceptance is assumed.
--
--   **Formalization Note** Arbitrary joint extensions are represented by a finite matrix factor on a general Hilbert space. Eve measurements lie in its commutant. The equality of effects retains all public registers in Eve's data.
-- source:
--   Secure quantum key distribution with an uncharacterized source, arXiv:quant-ph/0208155v2, PDF p. 3, Eqs. (2), (6)–(12), PDF pp.2–4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P04

noncomputable section

universe u v w

namespace QAlgorithms.Papers.Independent.Intakenext100.P04

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State IsTraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Advance50.P18 (keyEntropy)

open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Koashi–Preskill PDF pp.3–4, Eqs.(6)–(12): the circuit computes the same
key channel, cleans Q on the correctable support, and transfers the full joint
projected-state fidelity to the actual Q marginal. Printed Eq.(10) labels the
residual state inconsistently with Eq.(9); changed to the directly constructed
key effects, because U2 preserves Q's X label G-transpose(kappa_sif).
The normalization in Eq.(11) is (1/sqrt(2))^r, not an unspecified scalar. -/
theorem virtualCircuit_keyAndCleaning {N r : ℕ} (hN : 0 < N)
    (C : CorrectableEncoder N r) {I : Type v} (b : HilbertBasis I ℂ H)
    (rho : State b) (A : QubitFactor N H) :
    virtualCircuit C ∈ Matrix.unitaryGroup (Qubits N × Qubits r) ℂ ∧
    (∀ y, virtualKeyEffect C y = directKeyEffect C y) ∧
    (∀ x, x ∈ C.errors →
      act (virtualCircuit C) (tensorVec (ket x) (xBasisVector r 0)) =
        tensorVec
          ((((Real.sqrt 2)⁻¹ ^ r : ℝ) : ℂ) •
            ∑ y : Qubits r, ket (x + C.encoder y)) (ket (0 : Qubits r))) ∧
    (let sigma := qubitMarginal b rho A
     let P := A (correctableProjector C)
     let q := (operatorTrace b (P.comp rho.val.val)).re
     q ≤ (virtualOutput C sigma 0 0).re ∧
     (0 < q →
       IsTraceClass (projectedJointState b rho P) ∧
       IsPositive (projectedJointState b rho P) ∧
       operatorTrace b (projectedJointState b rho P) = 1 ∧
       squaredHilbertFidelity b (projectedJointState b rho P) rho.val.val = q) ∧
     (q = 1 → virtualOutput C sigma = zProjector r 0 ∧
       ∀ (n : ℕ) (M : EveMeasurement A n) (y : Qubits r) (z : Fin n),
         (operatorTrace b ((A (directKeyEffect C y)).comp
           ((M.effect z).comp rho.val.val))).re =
         ((2 : ℝ) ^ r)⁻¹ * (operatorTrace b ((M.effect z).comp rho.val.val)).re)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P04

end

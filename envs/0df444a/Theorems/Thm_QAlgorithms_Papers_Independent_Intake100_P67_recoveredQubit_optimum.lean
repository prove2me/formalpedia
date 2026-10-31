-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_recoveredQubit_optimum
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.recoveredQubit_optimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:20:07.293512+00:00
-- url     : https://prove2.me/theorems/f171477c-cf7f-45ee-8c6b-ea8d5b97579a
-- title:
--   Optimal deterministic recovered-qubit fidelity
-- statement:
--   Let $N\ge1$ be an integer. Alice and Bob share a normalized pure state $(O_A\otimes I_B)|\psi^-\rangle^{\otimes N}$, where $\operatorname{tr}(O^\dagger O)=2^N$ and $|\psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2$. Alice measures her $N$ qubits and an unknown input qubit with an $N$-outcome POVM, sends the outcome $i$, and Bob retains $B_i$ without a correcting operation. The resource and measurement are fixed independently of the input. Write $F$ for singlet entanglement fidelity and $f$ for fidelity averaged over Haar-distributed normalized pure inputs.
--
--   The resource specified by (34)–(35), with $O=\sqrt X$, and the completed generalized square-root measurement (32) attain
--
--   $$F_{\rm opt}=\cos^2\frac{\pi}{N+2},\qquad f_{\rm opt}=\frac23+\frac13\cos\frac{2\pi}{N+2}.$$
--
--   Every such resource and POVM satisfy $F\le F_{\rm opt}$ and $f\le f_{\rm opt}$. Thus these are attained optima over the whole stated protocol model.
--
--   This gives the exact best recovered-qubit fidelity for correction-free port selection.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 7, §IV B, Eqs. (32)–(42); Appendix C

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF pp.6–7, Eqs.(32)–(42), Appendix C p.12: simultaneous resource/POVM optimum.
The completed generalized SRM attains the upper bound over every physical resource/POVM.
Appendix C's final 2*cos^2(2*pi/(N+2)) is a factor-of-two-in-angle typo; its preceding
expression and the chosen dual a give 2*cos^2(pi/(N+2)), as required by Eq.(41). -/
theorem recoveredQubit_optimum (N : ℕ) (hN : 1 ≤ N) :
    IsDeterministicPortProtocol (resourceOperator (deterministicX N)) (deterministicMeasurement N) ∧
    entFidelity (resourceOperator (deterministicX N)) (deterministicMeasurement N) =
      deterministicOptimumFidelity N ∧
    portAverageFidelity (resourceOperator (deterministicX N)) (deterministicMeasurement N) =
      deterministicOptimumAverage N ∧
    (∀ (O : Matrix (Qubits N) (Qubits N) ℂ)
      (M : Fin N → Matrix (AC N) (AC N) ℂ), IsDeterministicPortProtocol O M →
        entFidelity O M ≤ deterministicOptimumFidelity N ∧ portAverageFidelity O M ≤ deterministicOptimumAverage N) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end

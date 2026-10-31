-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_aliceDimension_noAdvantage
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.aliceDimension_noAdvantage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:21:43.663281+00:00
-- url     : https://prove2.me/theorems/03587dde-9bbf-4cc5-8a87-beb9f15a71a2
-- title:
--   Extra Alice qubits give no fidelity advantage
-- statement:
--   Let $N_A\ge N\ge1$ be integers. Consider any normalized pure resource $(O\otimes I)|\psi^-\rangle^{\otimes N}$ with rectangular $O:\mathbb C^{2^N}\to\mathbb C^{2^{N_A}}$ and $\operatorname{tr}(O^\dagger O)=2^N$, together with any input-independent $N$-outcome POVM on Alice's $N_A$ qubits and input qubit. Bob simply retains the reported port.
--
--   There exist a square resource operator $O_0$ and a physical POVM on only $N$ Alice resource qubits and the input such that
--
--   $$F(O_0,\Pi^0)=F(O,\Pi),\qquad f(O_0,\Pi^0)=f(O,\Pi).$$
--
--   Here $F$ is singlet entanglement fidelity and $f=(2F+1)/3$ is normalized Haar average fidelity. The replacement resource is normalized and the replacement POVM is positive and complete, including when $O$ is singular.
--
--   Consequently additional Alice qubits cannot increase the deterministic optimum.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 3, §II, paragraph following Eq. (5)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF p.3, §II: extra Alice qubits do not improve average deterministic fidelity.
The small POVM is existentially reconstructed, including completion at singular O. -/
theorem aliceDimension_noAdvantage (N NA : ℕ) (hN : 1 ≤ N) (hNA : N ≤ NA)
    (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (M : Fin N → Matrix (AC NA) (AC NA) ℂ) (hM : IsDeterministicPortProtocol O M) :
    ∃ (Osmall : Matrix (Qubits N) (Qubits N) ℂ)
      (Msmall : Fin N → Matrix (AC N) (AC N) ℂ),
      IsDeterministicPortProtocol Osmall Msmall ∧ entFidelity Osmall Msmall = entFidelity O M ∧
        portAverageFidelity Osmall Msmall = portAverageFidelity O M := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end

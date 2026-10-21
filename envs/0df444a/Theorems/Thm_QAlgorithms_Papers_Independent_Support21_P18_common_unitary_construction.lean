-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P18_common_unitary_construction
-- name    : QAlgorithms.Papers.Independent.Support21.P18.common_unitary_construction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:49:39.030414+00:00
-- url     : https://prove2.me/theorems/505f57d4-9a27-49c1-9205-1ecd984df80a
-- title:
--   One common unitary realizes the explicit quantum output
-- statement:
--   Fix integers $N,M\ge1$. For a unit qubit vector $\psi=\alpha|0\rangle+\beta|1\rangle$, set $\psi^\perp=\overline\beta|0\rangle-\overline\alpha|1\rangle$. Braces denote normalized symmetric kets with the displayed multiplicities. Define the joint vector on $N+M$ clone sites and $M$ complement sites by
--   $$
--   q_{NM}(\psi)=\sum_{j=0}^{M}\gamma_j\,|\{(N+M-j)\psi;j\psi^\perp\}\rangle\otimes|\{(M-j)\psi^\perp;j\psi\}\rangle,
--   \qquad
--   \gamma_j=(-1)^j\binom{N+M-j}{N}^{1/2}\binom{N+M+1}{M}^{-1/2}.
--   $$
--   For every pair of unit vectors $\psi,\phi$, $\langle q_{NM}(\psi),q_{NM}(\phi)\rangle=\langle\psi,\phi\rangle^N$. There exist a normalized ancillary vector $X_{bc}$ on $M+M$ qubits and one unitary $U_{NM}$ on the $N+2M$ physical qubits such that simultaneously for every unit $\psi$,
--   $$
--   U_{NM}(|\psi\rangle^{\otimes N}\otimes X_{bc})=q_{NM}(\psi).
--   $$
--   This gives a physical realization of the explicit coherent-input transformation with a gate and ancilla independent of the unknown input.
-- source:
--   Optimal Manipulations with Qubits: Universal NOT Gate, arXiv:quant-ph/9901053v1, PDF p. 3, Quantum scenario, Eqs.(7),(8): one common unitary realizes the explicit output

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.3, Eqs.(7),(8): the explicit amplitudes preserve every coherent-input
inner product, and admit ONE full unitary extension with ONE normalized ancilla
chosen before the unknown input. No minimal-workspace claim is made. -/
theorem common_unitary_construction (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) :
    (∀ psi phi : EuclideanSpace ℂ (Fin 2), IsState psi → IsState phi →
      inner ℂ (quantumOutput N M psi) (quantumOutput N M phi) =
        inner ℂ psi phi ^ N) ∧
    ∃ X : EuclideanSpace ℂ (Qubits M × Qubits M), IsState X ∧
      ∃ U : Matrix.unitaryGroup (Qubits (N + M) × Qubits M) ℂ,
        ∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
          act U.val (gateInput N M psi X) = quantumOutput N M psi := by sorry

end QAlgorithms.Papers.Independent.Support21.P18

end

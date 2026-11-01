-- Prove2me | Theorems.Thm_ShendeQSD_Synthesis_cz_eq_cnot_conj
-- name    : ShendeQSD.Synthesis.cz_eq_cnot_conj
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:55.754832+00:00
-- url     : https://prove2.me/theorems/c532dd40-7518-446e-bb31-8b5019f61809
-- title:
--   Appendix A.1: controlled-Z from one CNOT and one-qubit gates (corrected: the two $R_y(\pm\pi/2)$ of the displayed circuits swapped)
-- statement:
--   Let $\mathrm{CZ}=\mathrm{diag}(1,1,1,-1)$ be the controlled-Z gate on two qubits.
--
--   1. There are one-qubit unitaries $u,v$ with $\mathrm{CZ}=(I\otimes v)\,\mathrm{CNOT}\,(I\otimes u)$, where the CNOT has control the first qubit and target the second.
--   2. There are one-qubit unitaries $u,v$ with $\mathrm{CZ}=(v\otimes I)\,\mathrm{CNOT}'\,(u\otimes I)$, where $\mathrm{CNOT}'$ has control the second qubit and target the first.
--   3. Explicitly,
--   $$
--   \mathrm{CZ}=(I\otimes R_y(\tfrac\pi2))\,\mathrm{CNOT}\,(I\otimes R_y(-\tfrac\pi2))=(R_y(\tfrac\pi2)\otimes I)\,\mathrm{CNOT}'\,(R_y(-\tfrac\pi2)\otimes I),
--   $$
--   that is, the circuit $R_y(-\pi/2)$ on the target, CNOT, $R_y(\pi/2)$ on the target.
--
--   So a controlled-Z costs one CNOT in either orientation, which lets Appendix A.1 trade CNOTs for controlled-Z gates in multiplexed $R_y$ circuits.
--
--   **Formalization Note** $R_y$ is the paper's (p. 5); the first qubit is the first tensor factor.
--
--   Differences from the source:
--   - correction: the displayed circuits apply R_y(π/2) to the target first and R_y(−π/2) last → R_y(−π/2) first and R_y(π/2) last; reason: with the paper's R_y (p. 5), R_y(−π/2) σ_x R_y(π/2) = −σ_z, so the printed circuit computes diag(1, 1, −1, 1), not controlled-Z; swapping the two angles gives σ_z and hence controlled-Z
--   - reading: "a single CNOT with the desired orientation, and one-qubit gates" → both orientations, with the one-qubit gates on the CNOT's target; reason: the page displays one circuit per orientation, each with its one-qubit gates on the target
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, Appendix A.1, Eq. (20) and the circuits below it, p. 16

import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_ShendeQSD_Synthesis_czLib
import Definitions.Def_ShendeQSD_Synthesis_ry

open scoped Kronecker

namespace ShendeQSD.Synthesis

open QAlgorithms

/-- **Appendix A.1: controlled-Z from a single CNOT and one-qubit gates (corrected: the signs of
the two `R_y(±π/2)` gates of the displayed circuits are swapped).**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
Appendix A.1, p. 16: "This gate can be implemented using a single CNOT with the desired
orientation, and one-qubit gates (whose physical realizations are typically simpler)", followed by
two circuits: `R_y(π/2)` on the target, a CNOT, `R_y(−π/2)` on the target, for each orientation of
the CNOT.

1. There are one-qubit unitaries `u, v` with `CZ = (I ⊗ v) · CNOT · (I ⊗ u)`, where the CNOT has
   control the first (top) qubit and target the second.
2. There are one-qubit unitaries `u, v` with `CZ = (v ⊗ I) · CNOT' · (u ⊗ I)`, where `CNOT'` has
   control the second qubit and target the first.
3. Explicitly (the displayed circuits, corrected): `CZ = (I ⊗ R_y(π/2)) · CNOT · (I ⊗ R_y(−π/2))`
   and `CZ = (R_y(π/2) ⊗ I) · CNOT' · (R_y(−π/2) ⊗ I)`, i.e. `R_y(−π/2)` is applied first.

**Formalization Note.** Correction: with the paper's own `R_y` (p. 5), the printed circuits
(`R_y(π/2)` first, `R_y(−π/2)` last) compute `R_y(−π/2) σ_x R_y(π/2) = −σ_z` on the target when the
control is `|1⟩`, i.e. `diag(1, 1, −1, 1)`, not controlled-Z; swapping the two angles gives
controlled-Z. Reading: "with the desired orientation" is read as "in either orientation", with the
one-qubit gates on the CNOT's target, as in the page's two circuits. -/
theorem cz_eq_cnot_conj :
    (∃ u ∈ Matrix.unitaryGroup Bool ℂ, ∃ v ∈ Matrix.unitaryGroup Bool ℂ,
      czMat = ((1 : Matrix Bool Bool ℂ) ⊗ₖ v) * cnot * ((1 : Matrix Bool Bool ℂ) ⊗ₖ u)) ∧
    (∃ u ∈ Matrix.unitaryGroup Bool ℂ, ∃ v ∈ Matrix.unitaryGroup Bool ℂ,
      czMat = (v ⊗ₖ (1 : Matrix Bool Bool ℂ)) * cnot.submatrix Prod.swap Prod.swap *
        (u ⊗ₖ (1 : Matrix Bool Bool ℂ))) ∧
    czMat = ((1 : Matrix Bool Bool ℂ) ⊗ₖ ry (Real.pi / 2)) * cnot *
      ((1 : Matrix Bool Bool ℂ) ⊗ₖ ry (-(Real.pi / 2))) ∧
    czMat = (ry (Real.pi / 2) ⊗ₖ (1 : Matrix Bool Bool ℂ)) * cnot.submatrix Prod.swap Prod.swap *
      (ry (-(Real.pi / 2)) ⊗ₖ (1 : Matrix Bool Bool ℂ)) := by sorry

end ShendeQSD.Synthesis

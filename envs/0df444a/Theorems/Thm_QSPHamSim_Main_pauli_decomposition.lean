-- Prove2me | Theorems.Thm_QSPHamSim_Main_pauli_decomposition
-- name    : QSPHamSim.Main.pauli_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:10.647992+00:00
-- url     : https://prove2.me/theorems/823b4650-ee7b-4d00-a5c4-a068b12420f1
-- title:
--   Eq. (1) — real Pauli decomposition of the rotation sequence
-- statement:
--   For any real angle $\theta$ and finite sequence of real phases, write $V_\phi(\theta)$ for the ordered product of the paper's qubit rotations. The four coefficients extracted from its entries are real and give the exact decomposition
--   $$
--   V_\phi(\theta)=A(\theta)I+iB(\theta)\sigma_z+iC(\theta)\sigma_x+iD(\theta)\sigma_y.
--   $$
--   This identifies the real response functions that Theorem 1 characterizes. The rotation at the first phase acts first, and every rotation has angle $\theta$ with the half angle in its exponential.
-- source:
--   Low, Chuang, Optimal Hamiltonian Simulation by Quantum Signal Processing, arXiv:1606.02685v2, p. 1, Eq. (1)

import Mathlib
import Definitions.Def_QSPHamSim_Main_Setting

set_option autoImplicit false

namespace QSPHamSim.Main

theorem pauli_decomposition (N : ℕ) (φ : Fin N → ℝ) (θ : ℝ) :
    let M := qspSeq N φ θ
    M = (compA M : ℂ) • (1 : QubitMatrix) +
      (Complex.I * (compB M : ℂ)) • sigmaZ +
      (Complex.I * (compC M : ℂ)) • sigmaX +
      (Complex.I * (compD M : ℂ)) • sigmaY := by sorry

end QSPHamSim.Main

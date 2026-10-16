-- Prove2me | Theorems.Thm_QSPHamSim_Main_plus_block_eq
-- name    : QSPHamSim.Main.plus_block_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:26.694986+00:00
-- url     : https://prove2.me/theorems/3499c4e2-7ec3-47d0-b044-83e338614aba
-- title:
--   Eqs. (3), (5), (6) — projected operator in the eigenbasis
-- statement:
--   Let $|u_l\rangle$ be the columns of a unitary matrix with real eigenphases $\theta_l$. Form $U_{\phi_k}=\sum_l R_{\phi_k}(\theta_l)\otimes|u_l\rangle\langle u_l|$ and the ordered product $V=U_{\phi_N}\cdots U_{\phi_1}$. Its $|+\rangle$ ancilla block is
--   $$
--   \langle+|V|+\rangle=\sum_l\bigl(A(\theta_l)+iC(\theta_l)\bigr)|u_l\rangle\langle u_l|,
--   $$
--   where $A,C$ are the real Pauli components of the single-qubit sequence.
--
--   This transfers the scalar response to every eigenspace of the input unitary. The formula holds for any finite dimension, including zero.
-- source:
--   Low, Chuang, Optimal Hamiltonian Simulation by Quantum Signal Processing, arXiv:1606.02685v2, p. 3, Eqs. (3), (5), (6)

import Mathlib
import Definitions.Def_QSPHamSim_Main_Setting

set_option autoImplicit false

namespace QSPHamSim.Main

theorem plus_block_eq (n N : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ)
    (θs : Fin n → ℝ) (φ : Fin N → ℝ) :
    plusBlock n (Vop n N u θs φ) =
      ∑ l : Fin n,
        (((compA (qspSeq N φ (θs l)) : ℂ) +
          (compC (qspSeq N φ (θs l)) : ℂ) * Complex.I) • proj n u l) := by sorry

end QSPHamSim.Main

-- Prove2me | Theorems.Thm_QFTMultiplication_Exact_fourier_state_copy
-- name    : QFTMultiplication.Exact.fourier_state_copy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:55:45.188921+00:00
-- url     : https://prove2.me/theorems/a1c72bef-2483-48e9-a166-eb77632e45b3
-- title:
--   Lemma 2.2 — Fourier-state copying
-- statement:
--   For $N=2^q$ write $|\phi_x\rangle=F_q|x\rangle$. There are absolute positive constants $C_g,C_a$ such that for every nonnegative integer $q$ a unitary primitive-gate circuit on designated registers $I,O$ and temporary qubits implements
--   $$
--   |\phi_x\rangle_I|0^q\rangle_O\longmapsto
--   |\phi_x\rangle_I|\phi_x\rangle_O
--   \quad(0\le x<N),\qquad |c|\le C_gq,\quad a\le C_aq.
--   $$
--   Every temporary qubit returns to zero. Register $O$ is the specified output and is not included among these temporary qubits. The allowed primitives are H, CNOT, and Equation (3) phases. This is a coherent copy operation on the orthogonal Fourier basis and supplies a retained input for checking a candidate Fourier label.
--
--   Differences from the source:
--   - encoding: O-bounds → positive real gate and auxiliary constants before every register size; reason: this is the family-level asymptotic meaning, with allowable dependence only on the fixed data
--   - encoding: integer labels 0≤x<2^q → q-bit strings in the published most-significant-bit-first bijection; reason: this is exactly the same finite basis, including q=0
-- source:
--   Chandrima Kayal, Rajat Mittal, Manaswi Paraashar, Nitin Saurabh, STOC 2027 submission #1075 (October 2026), Lemma 2.2, p. 6 (PDF p. 6)

import Definitions.Def_QFTMultiplication_Exact_Model

set_option autoImplicit false

namespace QFTMultiplication.Exact

open QAlgorithms

/-- Lemma 2.2, p.6. O is an output register; only a additional wires must return to zero. -/
theorem fourier_state_copy :
    ∃ Cg Ca : ℝ, 0 < Cg ∧ 0 < Ca ∧ ∀ q : ℕ,
      ∃ (a : ℕ) (c : Circuit baseGates ((q + q) + a)),
        c.unitary ∈ Matrix.unitaryGroup (Qubits ((q + q) + a)) ℂ ∧
        (∀ x : Qubits q, CleanMaps c
          (joinVec (fourierState q x) (zeroKet q))
          (joinVec (fourierState q x) (fourierState q x))) ∧
        (c.size : ℝ) ≤ Cg * q ∧ (a : ℝ) ≤ Ca * q := by sorry

end QFTMultiplication.Exact

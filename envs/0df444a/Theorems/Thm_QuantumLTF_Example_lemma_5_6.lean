-- Prove2me | Theorems.Thm_QuantumLTF_Example_lemma_5_6
-- name    : QuantumLTF.Example.lemma_5_6
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-15T20:38:01.70396+00:00
-- url     : https://prove2.me/theorems/568be123-bb9e-4b36-b613-9c0cfcc3b9d0
-- title:
--   Lemma 5.6 — Lipschitz unitary extensions of state families
-- statement:
--   For normalized states $|\psi_z\rangle$ whose overlap with the reference state is real and lies in $[0,1]$, one may choose unitary extensions $U_z|0\rangle=|\psi_z\rangle$ satisfying
--   $$\|U_z-U_{z'}\|\le2\sqrt2\,\||\psi_z\rangle-|\psi_{z'}\rangle\|.$$
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, STOC 2027 submission #347, Lemma 5.6, p. 77 (PDF p. 78).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Example_LowerModel

namespace QuantumLTF.Example

open QAlgorithms

theorem lemma_5_6 :
    ∀ {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (z0 : ι)
      (ψ : SignString m → EuclideanSpace ℂ ι),
      (∀ z, ‖ψ z‖ = 1) →
      (∀ z, (inner ℂ (ket z0) (ψ z)).im = 0 ∧ (inner ℂ (ket z0) (ψ z)).re ∈ Set.Icc 0 1) →
      ∃ U : SignString m → Matrix ι ι ℂ,
        (∀ z, U z ∈ Matrix.unitaryGroup ι ℂ ∧ act (U z) (ket z0) = ψ z) ∧
        ∀ z z', specNorm (U z - U z') ≤ 2 * Real.sqrt 2 * ‖ψ z - ψ z'‖ := by sorry

end QuantumLTF.Example

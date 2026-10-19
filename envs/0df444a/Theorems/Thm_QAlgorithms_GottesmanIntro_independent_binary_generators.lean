-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_independent_binary_generators
-- name    : QAlgorithms.GottesmanIntro.independent_binary_generators
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T16:14:18.656326+00:00
-- url     : https://prove2.me/theorems/522decae-4844-4fb5-acb1-f24ae16b60c6
-- title:
--   Independent stabilizer generators have independent binary Pauli labels
-- statement:
--   Let $g_1,\ldots,g_a$ generate an Abelian subgroup $S$ of the $n$-qubit Pauli group. Assume that $-I\notin S$ and that $|S|=2^a$.
--
--   There are Pauli strings $P_1,\ldots,P_a$, including their overall phases, whose matrices are the given generators. Write $x_i,z_i\in\mathbb F_2^n$ for their binary labels: the $X$ label is one at an $X$ or $Y$ factor, and the $Z$ label is one at a $Z$ or $Y$ factor. Then
--   $$
--   \{(x_1\mid z_1),\ldots,(x_a\mid z_a)\}\text{ is linearly independent over }\mathbb F_2.
--   $$
--
--   This is the independence step in the proof that every stabilizer error syndrome is realized by a Pauli error. It supplies the full row rank needed to solve the symplectic syndrome equations.
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation (2009), arXiv:0904.2557v1, PDF pp.12–13, binary representation preceding Lemma1 and independence assertion in the proof of Lemma1. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_QECC
import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace QAlgorithms.GottesmanIntro
open Stabilizer

theorem independent_binary_generators (n a : ℕ)
    (g : Fin a → Matrix.unitaryGroup (Qubits n) ℂ)
    (hS : IsStabilizerGroup (Subgroup.closure (Set.range g)))
    (hcard : Nat.card (Subgroup.closure (Set.range g)) = 2 ^ a) :
    ∃ P : Fin a → PauliString n,
      (∀ i, (g i : Matrix (Qubits n) (Qubits n) ℂ) = (P i).toMatrix) ∧
      LinearIndependent (ZMod 2) (fun i =>
        Sum.elim
          (fun q => (if (P i).ops q = Pauli.X ∨ (P i).ops q = Pauli.Y then 1 else 0 : ZMod 2))
          (fun q => (if (P i).ops q = Pauli.Z ∨ (P i).ops q = Pauli.Y then 1 else 0 : ZMod 2))) := by
  sorry
end QAlgorithms.GottesmanIntro

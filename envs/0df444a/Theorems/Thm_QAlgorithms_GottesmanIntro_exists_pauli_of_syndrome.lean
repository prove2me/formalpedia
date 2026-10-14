-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_exists_pauli_of_syndrome
-- name    : QAlgorithms.GottesmanIntro.exists_pauli_of_syndrome
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:57:59.703495+00:00
-- url     : https://prove2.me/theorems/ec4ce82d-5ad0-409c-8327-3861c3305465
-- title:
--   Every error syndrome of a stabilizer is realized by a Pauli error
-- statement:
--   Let $\mathcal P_n$ be the $n$-qubit Pauli group and let $g_1,\dots,g_a\in\mathcal P_n$ generate a stabilizer $S=\langle g_1,\dots,g_a\rangle$, that is, an Abelian subgroup of $\mathcal P_n$ with $-I\notin S$, and suppose the generators are independent, i.e. $|S|=2^a$. The error syndrome of a Pauli operator $E$ is the vector in $\mathbb F_2^a$ whose $i$-th bit is $0$ if $g_i$ commutes with $E$ and $1$ if it anticommutes.
--
--   Then for every $v\in\mathbb F_2^a$ there is $E\in\mathcal P_n$ with syndrome $v$:
--   $$g_iE=Eg_i\ \text{ if } v_i=0,\qquad g_iE=-Eg_i\ \text{ if } v_i=1\qquad(i=1,\dots,a).$$
--
--   This lemma is the step in the proof of the dimension count of stabilizer codes (Theorem 5) that shows all $2^a$ syndrome subspaces are nonempty.
--
--   **Formalization Note** The syndrome is relative to the generator list, as in the source's proof; the independence of the generators (used in the proof as linear independence of their binary vectors) is the hypothesis $|S|=2^a$. The anticommutation clause is stated explicitly.
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 12, Lemma 1. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_QECC
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro

open Stabilizer


/-- Gottesman intro p.12–13, Lemma 1: given a stabilizer `S` (an Abelian subgroup of `P_n`
with `−1 ∉ S`) with independent generators `g_1, …, g_a` (so `|S| = 2^a`), every error syndrome
`v ∈ F_2^a` is the syndrome of some Pauli operator `E`: `E` commutes with `g_i` when `v_i = 0`
and anticommutes with `g_i` when `v_i = 1`. -/
theorem exists_pauli_of_syndrome (n a : ℕ) (g : Fin a → Matrix.unitaryGroup (Qubits n) ℂ)
    (hS : IsStabilizerGroup (Subgroup.closure (Set.range g)))
    (hcard : Nat.card (Subgroup.closure (Set.range g)) = 2 ^ a) (v : Fin a → ZMod 2) :
    ∃ E ∈ pauliGroup n, ∀ i : Fin a,
      (v i = 0 → (g i : Matrix (Qubits n) (Qubits n) ℂ) * E = E * g i) ∧
      (v i = 1 → (g i : Matrix (Qubits n) (Qubits n) ℂ) * E = -((E : Matrix (Qubits n) (Qubits n) ℂ) * g i)) := by
  sorry

end QAlgorithms.GottesmanIntro

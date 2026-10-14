-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_corrects_linearCombination
-- name    : QAlgorithms.GottesmanIntro.corrects_linearCombination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T18:04:09.918973+00:00
-- url     : https://prove2.me/theorems/4bcef73c-d26d-4b4e-a8b8-975d40655eca
-- title:
--   Correctable errors are closed under linear combinations; weight-t Pauli errors give all t-qubit errors
-- statement:
--   Let $C$ be a quantum code on $n$ qubits, i.e. a linear subspace of $(\mathbb C^2)^{\otimes n}$. Say that $C$ corrects a set $\mathcal S$ of operators if there is one quantum operation $\mathcal R$ (a trace-preserving map $\rho\mapsto\sum_i R_i\rho R_i^\dagger$, $\sum_i R_i^\dagger R_i=I$) such that for every $E\in\mathcal S$ and every unit vector $|\psi\rangle\in C$,
--
--   $$
--   \mathcal R\big(E|\psi\rangle\langle\psi|E^\dagger\big)=\|E|\psi\rangle\|^2\,|\psi\rangle\langle\psi|.
--   $$
--
--   Then:
--
--   1. If $C$ corrects $\{A,B\}$, then $C$ corrects the whole linear span $\{aA+bB : a,b\in\mathbb C\}$.
--   2. For every $t$, if $C$ corrects every Pauli operator of weight at most $t$ (a tensor product of $I,X,Y,Z$ with a phase, at most $t$ factors different from $I$), then $C$ corrects every operator that acts on at most $t$ qubits. Such an operator has the form $M\otimes I$ for an arbitrary, not necessarily unitary, operator $M$ on a set of at most $t$ qubits.
--
--   The theorem reduces error correction to a basis of errors. It is why it suffices to correct the discrete Pauli errors in order to correct arbitrary, even continuous or non-unitary, errors on few qubits.
--
--   **Formalization Note** The factor $\|E|\psi\rangle\|^2$ is forced by trace preservation of $\mathcal R$. One recovery must serve all errors at once: this is the source's procedure (record the error, measure, invert). With separate recoveries the claim fails.
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 4, Theorem 2. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro

open scoped Matrix

open QAlgorithms Stabilizer


/-- Gottesman intro p.4, Theorem 2: for an `n`-qubit quantum code `C`, (1) if `C` corrects the
errors `A` and `B` (with one recovery operation), it corrects every linear combination of `A`
and `B` (all of them with one recovery operation); (2) if `C` corrects all Pauli errors of
weight at most `t`, it corrects all errors acting on at most `t` qubits (arbitrary, not
necessarily unitary, operators; p.5). -/
theorem corrects_linearCombination (n : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))) :
    (∀ A B : Matrix (Qubits n) (Qubits n) ℂ, Corrects C {A, B} →
      Corrects C (Submodule.span ℂ {A, B} : Set (Matrix (Qubits n) (Qubits n) ℂ))) ∧
    ∀ t : ℕ, Corrects C {M | ∃ P : PauliString n, P.weight ≤ t ∧ M = P.toMatrix} →
      Corrects C {E | ActsOnAtMost t E} := by
  sorry



end QAlgorithms.GottesmanIntro

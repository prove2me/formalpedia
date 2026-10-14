-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_noCloning
-- name    : QAlgorithms.GottesmanIntro.noCloning
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T18:03:48.592842+00:00
-- url     : https://prove2.me/theorems/f38f36bf-5767-4b21-91e9-7a65825933d6
-- title:
--   No-Cloning: no quantum operation copies every state
-- statement:
--   This is the No-Cloning theorem.
--
--   Let $\mathcal H$ be a finite-dimensional Hilbert space with $\dim\mathcal H\ge 2$. A quantum operation from $\mathcal H$ to $\mathcal H\otimes\mathcal H$ is a map on operators of the form
--
--   $$
--   \rho\mapsto\sum_i E_i\,\rho\,E_i^\dagger,\qquad \sum_i E_i^\dagger E_i=I,
--   $$
--
--   with finitely many operators $E_i:\mathcal H\to\mathcal H\otimes\mathcal H$. No quantum operation $\Phi$ satisfies
--
--   $$
--   \Phi\big(|\psi\rangle\langle\psi|\big)=\big(|\psi\rangle\otimes|\psi\rangle\big)\big(\langle\psi|\otimes\langle\psi|\big)
--   $$
--
--   for every unit vector $|\psi\rangle\in\mathcal H$.
--
--   The theorem shows that a quantum repetition code $|\psi\rangle\mapsto|\psi\rangle^{\otimes 3}$ cannot exist, which motivates the subspace codes of the following sections.
--
--   **Formalization Note** States enter as density matrices, so the copy is required only up to a global phase. The class of operations is the source's general quantum operation, eq. (23). It contains the unitary-with-blank-ancilla operations of the proof. The hypothesis $\dim\mathcal H\ge2$ excludes the one-dimensional space, where the identity map clones.
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 2, Theorem 1. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro

open scoped Matrix

open QAlgorithms Stabilizer

/-- Gottesman intro p.2, Theorem 1 (No-Cloning): on a Hilbert space of dimension at least 2,
no quantum operation (eq. (23), p.4–5) maps `|ψ⟩⟨ψ|` to `(|ψ⟩ ⊗ |ψ⟩)(⟨ψ| ⊗ ⟨ψ|)` for every
state `|ψ⟩`. -/
theorem noCloning {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : 2 ≤ Fintype.card ι)
    (Φ : Superop ι (ι × ι)) (hΦ : IsChannel Φ) :
    ¬ ∀ ψ : EuclideanSpace ℂ ι, IsState ψ → Φ (pureDensity ψ) = pureDensity (tensorVec ψ ψ) := by
  sorry




end QAlgorithms.GottesmanIntro

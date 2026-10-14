-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_knillLaflamme
-- name    : QAlgorithms.GottesmanIntro.knillLaflamme
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T18:03:31.463684+00:00
-- url     : https://prove2.me/theorems/9cb9c8c0-2d0b-45c8-bee0-2cea5eb5fbf1
-- title:
--   Knill–Laflamme condition for quantum error correction
-- statement:
--   This is the Knill–Laflamme criterion.
--
--   Let $\mathcal H$ be a finite-dimensional Hilbert space, $\mathcal E$ a linear space of operators on $\mathcal H$ (the errors) and $C\subseteq\mathcal H$ a subspace. Say $C$ corrects $\mathcal E$ if there is a quantum operation $\mathcal R$ on $\mathcal H$ (a map $\rho\mapsto\sum_i R_i\rho R_i^\dagger$ with $\sum_i R_i^\dagger R_i=I$) such that $\mathcal R(E|\psi\rangle\langle\psi|E^\dagger)=\|E|\psi\rangle\|^2|\psi\rangle\langle\psi|$ for all $E\in\mathcal E$ and all unit vectors $|\psi\rangle\in C$. Then $C$ corrects $\mathcal E$ if and only if there is a function $c:\mathcal E\to\mathbb C$ such that
--
--   $$
--   \langle\psi|E^\dagger E|\psi\rangle=c(E)\qquad\text{for all }E\in\mathcal E\text{ and all unit vectors }|\psi\rangle\in C.
--   $$
--
--   The criterion turns the existence of a recovery operation into a checkable condition on the code alone. It is the basis of the distance, degeneracy and counting bounds that follow.
--
--   **Formalization Note** The function $c$ is quantified before $|\psi\rangle$, so it does not depend on the state. Codewords are normalized, following the source's convention of omitted normalization (p.2).
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 6, Theorem 3. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro

open scoped Matrix

open QAlgorithms Stabilizer



/-- Gottesman intro p.6, Theorem 3 (Knill–Laflamme): for a linear space `𝓔` of errors on a
finite-dimensional Hilbert space `H` and a subspace `C` of `H`, `C` is a quantum
error-correcting code correcting `𝓔` iff there is a function `c(E)`, independent of the state,
with `⟨ψ|E†E|ψ⟩ = c(E)` for all `E ∈ 𝓔` and all normalized `|ψ⟩ ∈ C` (eq. (29)). -/
theorem knillLaflamme {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝓔 : Submodule ℂ (Matrix ι ι ℂ)) (C : Submodule ℂ (EuclideanSpace ℂ ι)) :
    Corrects C (𝓔 : Set (Matrix ι ι ℂ)) ↔
      ∃ c : Matrix ι ι ℂ → ℂ, ∀ E ∈ 𝓔, ∀ ψ ∈ C, ‖ψ‖ = 1 → inner ℂ ψ (act (Eᴴ * E) ψ) = c E := by
  sorry


end QAlgorithms.GottesmanIntro

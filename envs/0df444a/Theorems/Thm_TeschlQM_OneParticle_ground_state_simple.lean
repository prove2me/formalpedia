-- Prove2me | Theorems.Thm_TeschlQM_OneParticle_ground_state_simple
-- name    : TeschlQM.OneParticle.ground_state_simple
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T08:33:29.656634+00:00
-- url     : https://prove2.me/theorems/e8ab38fa-cdc9-47d1-9e13-d18812d189d7
-- title:
--   Theorem 10.12 — the ground state of H₀ + V is simple with a strictly positive eigenfunction
-- statement:
--   Let $V : \mathbb R^n \to \mathbb R$ be measurable and suppose $H = H_0 + V$ is self-adjoint and bounded from below with $C_c^\infty(\mathbb R^n)$ as a core. If
--   $$E_0 = \min \sigma(H)$$
--   is an eigenvalue, then it is simple and the corresponding eigenfunction is strictly positive.
--
--   The lowest eigenvalue is the ground state energy of the particle; nondegeneracy and positivity of the ground state are basic structural facts used throughout quantum mechanics. The hypotheses hold for the potentials of Theorem 10.2.
--
--   **Formalization Note.** $H$ is the `LinearPMap` sum of $H_0$ and the maximally defined multiplication operator $V$ on $\mathfrak D(H_0) \cap \mathfrak D(V)$. "$E_0 = \min\sigma(H)$" is $E_0 \in \sigma(H)$ together with $E_0 \le \operatorname{Re} z$ for all $z \in \sigma(H)$ (the spectrum of a self-adjoint operator is real). "Simple" is `Module.finrank ℂ (eigenspace H E₀) = 1`, and the eigenspace contains a function that is $> 0$ almost everywhere.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 236, Theorem 10.12

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator
import Definitions.Def_TeschlQM_OneParticle_freeHamiltonian
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_OneParticle_essentialSpectrum
import Definitions.Def_TeschlQM_OneParticle_IsBoundedBelow
import Definitions.Def_TeschlQM_OneParticle_testFunctions
import Definitions.Def_TeschlQM_OneParticle_positivity

namespace TeschlQM.OneParticle

/-- Teschl, Theorem 10.12, p. 236. Suppose `H = H₀ + V` is self-adjoint and bounded from below with
`C_c^∞(ℝⁿ)` as a core. If `E₀ = min σ(H)` is an eigenvalue, it is simple and the corresponding
eigenfunction is strictly positive.

`V : ℝⁿ → ℝ` is a measurable potential, `V` the maximally defined multiplication operator (2.21)
and `H₀ + V` the operator sum on `𝔇(H₀) ∩ 𝔇(V)`. `E₀ = min σ(H)`: `E₀ ∈ σ(H)` and
`E₀ ≤ Re z` for every `z ∈ σ(H)` (`σ(H) ⊆ ℝ` since `H` is self-adjoint). "Simple" means the
eigenspace `Ker(H - E₀)` is one-dimensional. -/
theorem ground_state_simple (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ) (hVm : Measurable V)
    (hsa : IsSelfAdjoint (freeHamiltonian n + multOp (fun x => (V x : ℂ))))
    (hbdd : IsBoundedBelow (freeHamiltonian n + multOp (fun x => (V x : ℂ))))
    (hcore : (freeHamiltonian n + multOp (fun x => (V x : ℂ))).HasCore (testFunctions n))
    (E₀ : ℝ) (hE₀ : (E₀ : ℂ) ∈ TeschlQM.Shared.spectrum (freeHamiltonian n + multOp (fun x => (V x : ℂ))))
    (hmin : ∀ z ∈ TeschlQM.Shared.spectrum (freeHamiltonian n + multOp (fun x => (V x : ℂ))), E₀ ≤ z.re)
    (heig : eigenspace (freeHamiltonian n + multOp (fun x => (V x : ℂ))) E₀ ≠ ⊥) :
    Module.finrank ℂ (eigenspace (freeHamiltonian n + multOp (fun x => (V x : ℂ))) E₀) = 1 ∧
      ∃ ψ ∈ eigenspace (freeHamiltonian n + multOp (fun x => (V x : ℂ))) E₀,
        IsStrictlyPositive ψ := by sorry

end TeschlQM.OneParticle

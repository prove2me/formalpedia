-- Prove2me | Theorems.Thm_SubsysAQEC_Sufficient_eq_5
-- name    : SubsysAQEC.Sufficient.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:15.567111+00:00
-- url     : https://prove2.me/theorems/15ae9204-a163-4994-8ef0-e4df638f5d5f
-- title:
--   Eq. (5), p. 2 — fidelity with a pure state: F(|ψ⟩, σ) = √⟨ψ|σ|ψ⟩
-- statement:
--   Let $\psi$ be a unit vector in a finite-dimensional Hilbert space, $\psi\equiv|\psi\rangle\langle\psi|$ the corresponding pure state, and $\sigma$ a positive semidefinite operator. The fidelity $F(\rho,\sigma)=\mathrm{tr}\sqrt{\rho^{1/2}\sigma\rho^{1/2}}$ with $\rho=\psi$ reduces to
--
--   $$F(|\psi\rangle,\sigma)=\sqrt{\langle\psi|\sigma|\psi\rangle}.$$
--
--   This is the form of the fidelity used throughout the paper's computation of the fidelity loss on pure code states, in particular in Eq. (14).
--
--   **Formalization Note** $F$ is the published root fidelity `WildeQIT.rootFidelity`, $\|\sqrt\rho\sqrt\sigma\|_1$. The paper states (5) for a state $\sigma$; the statement here only needs $\sigma$ positive semidefinite, which covers states.
-- source:
--   Mandayam, Ng, Towards a Unified Framework for Approximate Quantum Error Correction, arXiv:1202.5139v2, p. 2, (5)

import Mathlib
import Definitions.Def_SubsysAQEC_Sufficient_Setting

namespace SubsysAQEC.Sufficient

open Matrix WildeQIT
open scoped ComplexOrder

theorem eq_5 {n : Type} [Fintype n] [DecidableEq n] (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (σ : Matrix n n ℂ) (hσ : σ.PosSemidef) :
    rootFidelity (vecMulVec ψ (star ψ)) σ = Real.sqrt (star ψ ⬝ᵥ (σ *ᵥ ψ)).re := by sorry

end SubsysAQEC.Sufficient

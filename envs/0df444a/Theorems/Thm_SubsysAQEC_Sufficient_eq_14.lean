-- Prove2me | Theorems.Thm_SubsysAQEC_Sufficient_eq_14
-- name    : SubsysAQEC.Sufficient.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:31.271955+00:00
-- url     : https://prove2.me/theorems/17116ea4-0fbf-496f-ac6e-9dd29ab76147
-- title:
--   Eq. (14), proof of Theorem 2, p. 4 — fidelity of the transpose-channel recovery on a pure product state
-- statement:
--   Let $\mathcal E$ be a trace-preserving noise channel with Kraus operators $E_i:\mathcal H_{AB}\to\mathcal H$, and let $B_{ij},\Delta_{ij}$ satisfy (12), $PE_i^\dagger\mathcal E(P)^{-1/2}E_jP=P_A\otimes B_{ij}+\Delta_{ij}$. For unit vectors $\psi_A\in\mathcal H_A$, $\phi_B\in\mathcal H_B$, with $|\psi_A,\phi_B\rangle=|\psi_A\rangle\otimes|\phi_B\rangle$,
--
--   $$F^2\big[|\psi_A\rangle,(\mathrm{tr}_B\circ\mathcal R_P\circ\mathcal E)(|\psi_A,\phi_B\rangle\langle\psi_A,\phi_B|)\big]=1-\langle\psi_A,\phi_B|\sum_{ij}\Delta_{ij}^\dagger\big((P_A-|\psi_A\rangle\langle\psi_A|)\otimes P_B\big)\Delta_{ij}|\psi_A,\phi_B\rangle.$$
--
--   This computes the fidelity loss of the transpose channel at each pure product code state, and yields the expression (13) for $\eta_P$.
--
--   **Formalization Note** $F^2$ is the published `WildeQIT.fidelity`, with first argument the pure state $|\psi_A\rangle\langle\psi_A|$; $P_A,P_B$ are identity matrices. The real part is taken of the (real) expectation value.
-- source:
--   Mandayam, Ng, Towards a Unified Framework for Approximate Quantum Error Correction, arXiv:1202.5139v2, p. 4, (14)

import Mathlib
import Definitions.Def_SubsysAQEC_Sufficient_Setting

namespace SubsysAQEC.Sufficient

open Matrix QReversal.NearOpt PeresTerno WildeQIT
open scoped Kronecker

theorem eq_14 {a b o ι : Type} [Fintype a] [Fintype b] [Fintype o] [Fintype ι]
    [DecidableEq a] [DecidableEq b] [DecidableEq o]
    (E : ι → Matrix o (a × b) ℂ) (hE : IsTPNoise E)
    (B : ι → ι → Matrix b b ℂ) (Δ : ι → ι → Matrix (a × b) (a × b) ℂ)
    (h12 : ∀ i j, (E i)ᴴ * invSqrt (noiseOfP E) * E j = (1 : Matrix a a ℂ) ⊗ₖ B i j + Δ i j)
    (ψ : a → ℂ) (φ : b → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (hφ : star φ ⬝ᵥ φ = 1) :
    fidelity (vecMulVec ψ (star ψ))
        (partialTraceRight (krausUpdate (transposeKraus E)
          (krausUpdate E (vecMulVec (prodVec ψ φ) (star (prodVec ψ φ)))))) =
      1 - (star (prodVec ψ φ) ⬝ᵥ ((∑ i, ∑ j, (Δ i j)ᴴ *
        ((1 - vecMulVec ψ (star ψ)) ⊗ₖ (1 : Matrix b b ℂ)) * Δ i j) *ᵥ prodVec ψ φ)).re := by sorry

end SubsysAQEC.Sufficient

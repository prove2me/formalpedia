-- Prove2me | Theorems.Thm_SubsysAQEC_Sufficient_tp_relation
-- name    : SubsysAQEC.Sufficient.tp_relation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:08.851801+00:00
-- url     : https://prove2.me/theorems/9de15a84-0462-460f-8855-903a828502e6
-- title:
--   Proof of Theorem 2, p. 4 — the TP condition on R_P ∘ ℰ in terms of B_ij and Δ_ij
-- statement:
--   Let $\mathcal E$ be a trace-preserving noise channel with Kraus operators $E_i:\mathcal H_{AB}\to\mathcal H$, and suppose operators $B_{ij}$ on $\mathcal H_B$ and $\Delta_{ij}$ on $\mathcal H_{AB}$ satisfy (12):
--   $$PE_i^\dagger\mathcal E(P)^{-1/2}E_jP=P_A\otimes B_{ij}+\Delta_{ij}\quad\text{for all } i,j.$$
--   Then
--
--   $$P=\sum_{ij}\Big[P_A\otimes B_{ij}^\dagger B_{ij}+\Delta_{ij}^\dagger\Delta_{ij}+(P_A\otimes B_{ij}^\dagger)\Delta_{ij}+\Delta_{ij}^\dagger(P_A\otimes B_{ij})\Big].$$
--
--   This is the trace-preservation of $\mathcal R_P\circ\mathcal E$ written in the decomposition (12); it is the identity used to evaluate the fidelity in (14).
--
--   **Formalization Note** $P$ and $P_A$ are identity matrices, and $P_A\otimes X$ is the Kronecker product `1 ⊗ₖ X` (A first). The decomposition (12) is arbitrary: any $B_{ij}$ determines $\Delta_{ij}$.
-- source:
--   Mandayam, Ng, Towards a Unified Framework for Approximate Quantum Error Correction, arXiv:1202.5139v2, p. 4, proof of Theorem 2 (TP relation)

import Mathlib
import Definitions.Def_SubsysAQEC_Sufficient_Setting

namespace SubsysAQEC.Sufficient

open Matrix QReversal.NearOpt
open scoped Kronecker

theorem tp_relation {a b o ι : Type} [Fintype a] [Fintype b] [Fintype o] [Fintype ι]
    [DecidableEq a] [DecidableEq b] [DecidableEq o]
    (E : ι → Matrix o (a × b) ℂ) (hE : IsTPNoise E)
    (B : ι → ι → Matrix b b ℂ) (Δ : ι → ι → Matrix (a × b) (a × b) ℂ)
    (h12 : ∀ i j, (E i)ᴴ * invSqrt (noiseOfP E) * E j = (1 : Matrix a a ℂ) ⊗ₖ B i j + Δ i j) :
    ∑ i, ∑ j, ((1 : Matrix a a ℂ) ⊗ₖ ((B i j)ᴴ * B i j) + (Δ i j)ᴴ * Δ i j
      + ((1 : Matrix a a ℂ) ⊗ₖ (B i j)ᴴ) * Δ i j + (Δ i j)ᴴ * ((1 : Matrix a a ℂ) ⊗ₖ B i j)) = 1 := by sorry

end SubsysAQEC.Sufficient

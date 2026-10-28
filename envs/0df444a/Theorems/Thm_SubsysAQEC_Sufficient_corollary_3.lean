-- Prove2me | Theorems.Thm_SubsysAQEC_Sufficient_corollary_3
-- name    : SubsysAQEC.Sufficient.corollary_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:14.932796+00:00
-- url     : https://prove2.me/theorems/e2c617ef-ccba-42db-bcc2-a47825f09139
-- title:
--   Corollary 3, p. 4 — C is ϵ-correctable on A, by the transpose channel, whenever ϵ ≥ ‖Σ_ij Δ_ij^† Δ_ij‖
-- statement:
--   Let $\mathcal E$ be a CPTP noise channel with Kraus operators $E_i:\mathcal H_{AB}\to\mathcal H$ acting on the subsystem code $\mathcal C=\{\rho_A\otimes\rho_B\}$, and suppose
--   $$PE_i^\dagger\mathcal E(P)^{-1/2}E_jP=P_A\otimes B_{ij}+\Delta_{ij}\qquad(12)$$
--   for all $i,j$, with $B_{ij}\in\mathcal B(\mathcal H_B)$, $\Delta_{ij}\in\mathcal B(\mathcal H_{AB})$, the inverse square root taken on the support of $\mathcal E(P)$. If
--
--   $$\epsilon\ \ge\ \Big\|\sum_{ij}\Delta^\dagger_{ij}\Delta_{ij}\Big\|,\qquad(15)$$
--
--   with $\|\cdot\|$ the operator norm, then $\mathcal C$ is $\epsilon$-correctable on $A$ under $\mathcal E$. More precisely: the transpose channel $\mathcal R_P$, with Kraus operators $R^P_i=PE_i^\dagger\mathcal E(P)^{-1/2}$, is a recovery (trace preserving on the support $\mathcal P_{\mathcal E}$ of $\mathcal E(P)$), and its fidelity loss on every code state $\rho_A\otimes\rho_B$ is at most $\|\sum_{ij}\Delta^\dagger_{ij}\Delta_{ij}\|$.
--
--   Corollary 3 is the paper's easily checkable sufficient condition for approximate subsystem codes: any choice of the operators $B_{ij}$ gives a bound, and the recovery achieving it is explicit.
--
--   **Formalization Note** The noise's Kraus operators are rectangular matrices from $\mathcal H_{AB}$ into $\mathcal H$, so $P$ and $P_A$ are identity matrices; the operator norm is Mathlib's $\ell^2$ operator norm (`Matrix.Norms.L2Operator`). $\epsilon$-correctability is the existence of a recovery with fidelity loss at most $\epsilon$ on every code state, mixed ones included. No smallness of $\Delta_{ij}$ and no full support of $\mathcal E(P)$ is assumed.
-- source:
--   Mandayam, Ng, Towards a Unified Framework for Approximate Quantum Error Correction, arXiv:1202.5139v2, p. 4, Corollary 3, (15)

import Mathlib
import Definitions.Def_SubsysAQEC_Sufficient_Setting

namespace SubsysAQEC.Sufficient

open Matrix QReversal.NearOpt PeresTerno
open scoped Kronecker Matrix.Norms.L2Operator

theorem corollary_3 {a b o ι : Type} [Fintype a] [Fintype b] [Fintype o] [Fintype ι]
    [DecidableEq a] [DecidableEq b] [DecidableEq o]
    (E : ι → Matrix o (a × b) ℂ) (hE : IsTPNoise E)
    (B : ι → ι → Matrix b b ℂ) (Δ : ι → ι → Matrix (a × b) (a × b) ℂ)
    (h12 : ∀ i j, (E i)ᴴ * invSqrt (noiseOfP E) * E j = (1 : Matrix a a ℂ) ⊗ₖ B i j + Δ i j)
    (ε : ℝ) (hε : ‖∑ i, ∑ j, (Δ i j)ᴴ * Δ i j‖ ≤ ε) :
    IsEpsCorrectable E ε ∧ IsRecovery E (transposeKraus E) ∧
      ∀ (ρA : Matrix a a ℂ) (ρB : Matrix b b ℂ), IsDensityMatrix ρA → IsDensityMatrix ρB →
        fidelityLoss E (transposeKraus E) ρA ρB ≤ ‖∑ i, ∑ j, (Δ i j)ᴴ * Δ i j‖ := by sorry

end SubsysAQEC.Sufficient

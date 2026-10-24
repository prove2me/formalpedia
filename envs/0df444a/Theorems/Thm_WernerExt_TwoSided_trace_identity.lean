-- Prove2me | Theorems.Thm_WernerExt_TwoSided_trace_identity
-- name    : WernerExt.TwoSided.trace_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:22.178544+00:00
-- url     : https://prove2.me/theorems/2341f1ce-1f3a-45b4-97d9-c134931c3b88
-- title:
--   p. 2, Extendibility as a ground state problem — normalized eigenprojectors of H_W extend ρ_W(e), and Tr(ρ̂ H_W) = α for every extension ρ̂ of ρ_W(α)
-- statement:
--   Let $d\ge2$, $n_A,n_B\ge1$.
--
--   1. Every eigenvalue $e$ of $H^W$ lies in $[-1,1]$, and if $P_e$ is the orthogonal projector onto the eigenspace $\ker(H^W-e)$, then $P_e/\operatorname{Tr}P_e$ is an $(n_A,n_B)$-extension of the Werner state $\rho^W(e)$.
--   2. If $\alpha\in[-1,1]$ and $\hat\rho$ is an $(n_A,n_B)$-extension of $\rho^W(\alpha)$, then $$\operatorname{Tr}(\hat\rho\,H^W)=\alpha.$$
--
--   Together these identify the smallest eigenvalue of $H^W$ with the extremal extendible Werner parameter.
--
--   **Formalization Note** The eigenprojector is characterized as any $P$ with $P^2=P$, $P^\dagger=P$ whose fixed vectors are exactly the solutions of $H^Wv=ev$; such a $P$ exists and is unique.
--
--   Differences from the source:
--   - generalization: the normalized eigenprojectors are extensions of “certain Werner states” → the normalized projector onto the e-eigenspace is an extension of ρ_W(e), with e ∈ [−1, 1]; reason: the parameter is forced by clause 2 (Tr(P_e H_W)/Tr P_e = e) and the paper's next sentence uses exactly this; the Lean statement specializes to “some Werner state”
--   - encoding: eigenprojector of H_W → any Hermitian idempotent P whose fixed vectors are the solutions of H_W v = e v; reason: characterizes the orthogonal projector onto the eigenspace uniquely
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, p. 2, *Extendibility as a ground state problem*, 'The normalized eigenprojectors of H^W are …'

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model

namespace WernerExt.TwoSided

open Matrix
open scoped Kronecker ComplexOrder

/-- p. 2, *Extendibility as a ground state problem*: (a) every eigenvalue `e` of `H_W` lies in
`[−1, 1]`, and the orthogonal projector `P_e` onto its eigenspace, normalized by its trace, is
an `(nA, nB)`-extension of `ρ_W(e)`; (b) if `ρ̂` is an `(nA, nB)`-extension of `ρ_W(α)`, then
`Tr(ρ̂ H_W) = α`. -/
theorem trace_identity (d nA nB : ℕ) (hd : 2 ≤ d) (hA : 1 ≤ nA) (hB : 1 ≤ nB) :
    (∀ e : ℝ, IsEigenvalue (hamW d nA nB) e →
        e ∈ Set.Icc (-1 : ℝ) 1 ∧
          ∀ P : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ, P * P = P → Pᴴ = P →
            (∀ v : Cfg d nA nB → ℂ, P.mulVec v = v ↔ (hamW d nA nB).mulVec v = (e : ℂ) • v) →
            IsExtensionOf ((P.trace)⁻¹ • P) (wernerState d e)) ∧
      (∀ α ∈ Set.Icc (-1 : ℝ) 1, ∀ X : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ,
        IsExtensionOf X (wernerState d α) → (X * hamW d nA nB).trace = (α : ℂ)) := by sorry

end WernerExt.TwoSided

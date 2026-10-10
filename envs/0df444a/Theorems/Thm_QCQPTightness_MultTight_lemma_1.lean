-- Prove2me | Theorems.Thm_QCQPTightness_MultTight_lemma_1
-- name    : QCQPTightness.MultTight.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:20:21.015212+00:00
-- url     : https://prove2.me/theorems/3b178c10-7131-42c9-8632-b6db08ac2a5e
-- title:
--   Lemma 1, p. 7 — 𝒟_SDP = {(x, t) : sup_{γ∈Γ} q(γ, x) ≤ 2t} and Opt_SDP = min_x sup_{γ∈Γ} q(γ, x)
-- statement:
--   Consider a QCQP with data $(A_i,b_i,c_i)_{i=0}^m$, its Shor SDP relaxation with optimal value $\mathrm{Opt}_{\mathrm{SDP}}$ and projected epigraph $\mathcal D_{\mathrm{SDP}}$, the Lagrangian $q(\gamma,x) = q_0(x)+\sum_{i=1}^m\gamma_iq_i(x)$, and the dual object $\Gamma=\{\gamma : A(\gamma)\succeq 0,\ \gamma_i\ge 0\ \forall i\in[\![m_I]\!]\}$. Suppose Assumption 1 holds. Then
--
--   $$\mathcal D_{\mathrm{SDP}} = \Big\{(x,t) : \sup_{\gamma\in\Gamma} q(\gamma,x)\le 2t\Big\}\qquad\text{and}\qquad \mathrm{Opt}_{\mathrm{SDP}} = \min_{x\in\mathbb R^N}\ \sup_{\gamma\in\Gamma} q(\gamma,x),$$
--
--   where the minimum is attained.
--
--   The lemma rewrites the SDP relaxation through the dual object $\Gamma$; the proof of Theorem 8 uses both identities to show that points of $\mathcal D_{\mathrm{SDP}}\cap H$ attain the inner supremum.
--
--   **Formalization Note** $\sup_{\gamma\in\Gamma}q(\gamma,x)\le 2t$ is written as $q(\gamma,x)\le 2t$ for all $\gamma\in\Gamma$. The value identity is stated in `EReal`, with $\sup$ and $\inf$ as `⨆`/`⨅`, and "min" as an extra conjunct: some $x$ attains $\mathrm{Opt}_{\mathrm{SDP}}$. The standing assumption $m\ge 1$ is not needed and is dropped.
-- source:
--   arXiv:1911.09195v3, Lemma 1, p. 7

import Mathlib
import Definitions.Def_QCQPTightness_MultTight_QCQP

namespace QCQPTightness.MultTight

open QCQP Matrix

/-- Lemma 1 (arXiv:1911.09195v3, p. 7): under Assumption 1,
`𝒟_SDP = {(x, t) : sup_{γ∈Γ} q(γ, x) ≤ 2t}` and `Opt_SDP = min_x sup_{γ∈Γ} q(γ, x)`
(the minimum is attained). -/
theorem lemma_1 {N m : ℕ} (P : QCQP N m) (h1 : P.Assumption1) :
    P.DSDP = {p | ∀ γ ∈ P.Gamma, P.qγ γ p.1 ≤ 2 * p.2} ∧
      P.OptSDP = ⨅ x, ⨆ γ ∈ P.Gamma, ((P.qγ γ x : ℝ) : EReal) ∧
      ∃ x, P.OptSDP = ⨆ γ ∈ P.Gamma, ((P.qγ γ x : ℝ) : EReal) := by sorry

end QCQPTightness.MultTight

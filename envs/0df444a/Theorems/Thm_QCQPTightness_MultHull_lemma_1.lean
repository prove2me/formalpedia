-- Prove2me | Theorems.Thm_QCQPTightness_MultHull_lemma_1
-- name    : QCQPTightness.MultHull.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:12.014369+00:00
-- url     : https://prove2.me/theorems/94484476-8f5f-4495-8f06-2eafd100d1b8
-- title:
--   Lemma 1, p. 7 — 𝒟_SDP = {(x, t) : sup_{γ∈Γ} q(γ, x) ≤ 2t} and Opt_SDP = min_x sup_{γ∈Γ} q(γ, x)
-- statement:
--   Consider a QCQP (1) with data $(A_i, b_i, c_i)_{i=0}^m$, its Lagrangian $q(\gamma, x) = q_0(x)+\sum_{i=1}^m\gamma_iq_i(x)$, the dual object $\Gamma = \{\gamma : A(\gamma)\succeq 0,\ \gamma_i\ge 0\ \forall i\in[\![m_I]\!]\}$, and the projected epigraph $\mathcal D_{\mathrm{SDP}}$ and value $\mathrm{Opt}_{\mathrm{SDP}}$ of the Shor relaxation. Suppose Assumption 1 holds (the QCQP is feasible and $A(\gamma^*)\succ0$ for some $\gamma^*$ that is nonnegative on the inequality indices). Then
--
--   $$\mathcal D_{\mathrm{SDP}} = \Big\{(x,t) : \sup_{\gamma\in\Gamma} q(\gamma,x)\le 2t\Big\}\qquad\text{and}\qquad \mathrm{Opt}_{\mathrm{SDP}} = \min_{x\in\mathbb R^N}\sup_{\gamma\in\Gamma}q(\gamma,x).$$
--
--   The lemma rewrites the SDP relaxation entirely in terms of the dual object $\Gamma$; the second identity goes back to Fujie and Kojima. In the proof of Theorem 7 the first identity turns a point of $\mathcal D_{\mathrm{SDP}}$ into a bound $\sup_{\gamma\in\Gamma}q(\gamma,\hat x)\le 2\hat t$.
--
--   **Formalization Note** "$\sup_{\gamma\in\Gamma}q(\gamma,x)\le 2t$" is written as $q(\gamma,x)\le 2t$ for every $\gamma\in\Gamma$, which is equivalent also when the supremum is $+\infty$. $\mathrm{Opt}_{\mathrm{SDP}}$ and the suprema are taken in the extended reals; "min" is stated as the identity with the infimum over $x$ together with the existence of an $x$ attaining it. The paper's standing assumption $m\ge 1$ is not needed and is dropped.
-- source:
--   arXiv:1911.09195v3, Lemma 1, p. 7

import Mathlib
import Definitions.Def_QCQPTightness_MultHull_QCQP

namespace QCQPTightness.MultHull

open Matrix

theorem lemma_1 {N m : ℕ} (P : QCQP N m) (h1 : P.Assumption1) :
    P.DSDP = {p | ∀ γ ∈ P.Gamma, P.qγ γ p.1 ≤ 2 * p.2} ∧
    P.OptSDP = (⨅ x : Fin N → ℝ, ⨆ γ ∈ P.Gamma, ((P.qγ γ x : ℝ) : EReal)) ∧
    ∃ x : Fin N → ℝ, P.OptSDP = ⨆ γ ∈ P.Gamma, ((P.qγ γ x : ℝ) : EReal) := by sorry

end QCQPTightness.MultHull

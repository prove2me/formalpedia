-- Prove2me | Theorems.Thm_QCQPTightness_ConvHull_lemma_1
-- name    : QCQPTightness.ConvHull.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:36.113882+00:00
-- url     : https://prove2.me/theorems/3f5bff9b-6c2e-497a-a2c9-42ae4520708f
-- title:
--   Lemma 1, p. 7 — under Assumption 1, 𝒟_SDP = {(x, t) : sup_{γ∈Γ} q(γ, x) ≤ 2t} and Opt_SDP = min_x sup_{γ∈Γ} q(γ, x)
-- statement:
--   Let a QCQP (1) satisfy Assumption 1: it is feasible, and some $\gamma^*$, nonnegative on the inequality constraints, has $A(\gamma^*)\succ0$. Let $\Gamma$ be the dual object and $q(\gamma,x)=q_0(x)+\sum_i\gamma_iq_i(x)$ the Lagrangian. Then the projected SDP epigraph and the SDP value are described by $\Gamma$ alone:
--   $$\mathcal D_{\mathrm{SDP}}=\Big\{(x,t):\ \sup_{\gamma\in\Gamma}q(\gamma,x)\le 2t\Big\},\qquad \mathrm{Opt}_{\mathrm{SDP}}=\min_{x\in\mathbb R^N}\ \sup_{\gamma\in\Gamma}q(\gamma,x),$$
--   and the minimum over $x$ is attained.
--
--   This rewriting is the entry point of the paper's framework: every later statement about $\mathcal D_{\mathrm{SDP}}$ is read through the faces of $\Gamma$. The value identity goes back to Fujie and Kojima.
--
--   **Formalization Note.** "$\sup_{\gamma}q(\gamma,x)\le2t$" is written as $q(\gamma,x)\le2t$ for every $\gamma\in\Gamma$, which is equivalent also when the supremum is $+\infty$. The value identity is stated in `EReal` as an infimum over $x$ of the supremum over $\Gamma$, together with the existence of an $x$ attaining it (the "min"). The standing assumption $m\ge1$ is not needed and is omitted, which makes the statement stronger.
-- source:
--   arXiv:1911.09195v3, Lemma 1, p. 7

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP

namespace QCQPTightness.ConvHull

/-- Lemma 1 (arXiv:1911.09195v3, p. 7). Under Assumption 1,
`𝒟_SDP = {(x, t) : sup_{γ∈Γ} q(γ, x) ≤ 2t}` and `Opt_SDP = min_x sup_{γ∈Γ} q(γ, x)`;
the last conjunct says the minimum over `x` is attained. -/
theorem lemma_1 {N m : ℕ} (P : QCQP N m) (h1 : P.Assumption1) :
    P.DSDP = {p | ∀ γ ∈ P.Gamma, P.qγ γ p.1 ≤ 2 * p.2} ∧
    P.OptSDP = (⨅ x : Fin N → ℝ, ⨆ γ ∈ P.Gamma, ((P.qγ γ x : ℝ) : EReal)) ∧
    ∃ x : Fin N → ℝ, P.OptSDP = (⨆ γ ∈ P.Gamma, ((P.qγ γ x : ℝ) : EReal)) := by sorry

end QCQPTightness.ConvHull

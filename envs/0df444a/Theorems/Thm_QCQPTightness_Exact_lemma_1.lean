-- Prove2me | Theorems.Thm_QCQPTightness_Exact_lemma_1
-- name    : QCQPTightness.Exact.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:20:43.449082+00:00
-- url     : https://prove2.me/theorems/a7ab24a9-b724-4b88-9543-dcc1608f389e
-- title:
--   Lemma 1, p. 7 — 𝒟_SDP = {(x, t) : sup_{γ∈Γ} q(γ, x) ≤ 2t} and Opt_SDP = min_x sup_{γ∈Γ} q(γ, x)
-- statement:
--   Consider a QCQP with dual object $\Gamma$ and Lagrangian $q(\gamma,x)$, and suppose Assumption 1 holds: the QCQP is feasible and some $\gamma^*$ with $\gamma^*_i\ge0$ for $i\in[\![m_I]\!]$ has $A(\gamma^*)\succ 0$. Then the projected epigraph of the SDP relaxation and its value are
--
--   $$\mathcal D_{\mathrm{SDP}}=\Big\{(x,t) : \sup_{\gamma\in\Gamma}q(\gamma,x)\le 2t\Big\},\qquad \mathrm{Opt}_{\mathrm{SDP}}=\min_{x\in\mathbb R^N}\sup_{\gamma\in\Gamma}q(\gamma,x),$$
--
--   and the minimum is attained.
--
--   This describes the SDP relaxation entirely through $\Gamma$. The value identity goes back to Fujie and Kojima.
--
--   **Formalization Note** "$\sup_\gamma q(\gamma,x)\le 2t$" is written as $q(\gamma,x)\le 2t$ for every $\gamma\in\Gamma$, which is equivalent also when the supremum is $+\infty$. The value identity is stated in `EReal` as an infimum over $x$ of the supremum over $\Gamma$, together with the existence of an $x$ attaining it (the page's "min").
-- source:
--   arXiv:1911.09195v3, Lemma 1, p. 7

import Mathlib
import Definitions.Def_QCQPTightness_Exact_QCQP

namespace QCQPTightness.Exact
theorem lemma_1 {N m : ℕ} (P : QCQP N m) (h1 : P.Assumption1) :
    P.DSDP = {p | ∀ γ ∈ P.Gamma, P.qγ γ p.1 ≤ 2 * p.2} ∧
      P.OptSDP = ⨅ x : Fin N → ℝ, ⨆ γ ∈ P.Gamma, ((P.qγ γ x : ℝ) : EReal) ∧
      ∃ x : Fin N → ℝ, P.OptSDP = ⨆ γ ∈ P.Gamma, ((P.qγ γ x : ℝ) : EReal) := by sorry
end QCQPTightness.Exact

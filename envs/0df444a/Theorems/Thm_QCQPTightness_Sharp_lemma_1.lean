-- Prove2me | Theorems.Thm_QCQPTightness_Sharp_lemma_1
-- name    : QCQPTightness.Sharp.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:20:30.868585+00:00
-- url     : https://prove2.me/theorems/ca1564be-b699-4ba4-acf4-f19294a5ff0f
-- title:
--   Lemma 1, p. 7 — 𝒟_SDP = {(x, t) : sup_{γ∈Γ} q(γ, x) ≤ 2t} and Opt_SDP = min_x sup_{γ∈Γ} q(γ, x)
-- statement:
--   Let a QCQP satisfy Assumption 1. Then the projected epigraph of its SDP relaxation is described by the Lagrangian dual set $\Gamma$:
--   $$
--   \mathcal D_{\mathrm{SDP}}=\Big\{(x,t) : \sup_{\gamma\in\Gamma}q(\gamma,x)\le 2t\Big\}
--   \qquad\text{and}\qquad
--   \mathrm{Opt}_{\mathrm{SDP}}=\min_{x\in\mathbb R^N}\ \sup_{\gamma\in\Gamma}q(\gamma,x),
--   $$
--   where the minimum over $x$ is attained.
--
--   This is the paper's basic tool: it turns questions about the SDP relaxation into questions about the convex function $x\mapsto\sup_{\gamma\in\Gamma}q(\gamma,x)$, and is how the optimal values of the examples in §4.3 are computed.
--
--   **Formalization Note** The condition $\sup_{\gamma\in\Gamma}q(\gamma,x)\le 2t$ is written as $q(\gamma,x)\le2t$ for all $\gamma\in\Gamma$; the suprema and the infimum are taken in `EReal`, and "min" is stated as the infimum identity together with the existence of an $x$ attaining it. The standing assumption $m\ge1$ (p. 1) is a hypothesis.
-- source:
--   arXiv:1911.09195v3, Lemma 1, p. 7

import Mathlib
import Definitions.Def_QCQPTightness_Sharp_QCQP

namespace QCQPTightness.Sharp

/-- Lemma 1 (arXiv:1911.09195v3, p. 7): under Assumption 1,
`𝒟_SDP = {(x, t) : sup_{γ∈Γ} q(γ, x) ≤ 2t}` and `Opt_SDP = min_x sup_{γ∈Γ} q(γ, x)`
(the infimum over `x` is attained). -/
theorem lemma_1 {N m : ℕ} (P : QCQP N m) (hm : 1 ≤ m) (h1 : P.Assumption1) :
    P.DSDP = {p | ∀ γ ∈ P.Gamma, P.qγ γ p.1 ≤ 2 * p.2} ∧
    P.OptSDP = (⨅ x : Fin N → ℝ, ⨆ γ ∈ P.Gamma, ((P.qγ γ x : ℝ) : EReal)) ∧
    ∃ x : Fin N → ℝ, P.OptSDP = ⨆ γ ∈ P.Gamma, ((P.qγ γ x : ℝ) : EReal) := by sorry

end QCQPTightness.Sharp

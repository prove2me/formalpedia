-- Prove2me | Theorems.Thm_QCQPTightness_ConvHull_theorem_1
-- name    : QCQPTightness.ConvHull.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:31:23.295586+00:00
-- url     : https://prove2.me/theorems/5e500d27-f682-4d52-b634-9dce3eff6670
-- title:
--   Theorem 1, p. 13 — for polyhedral Γ with dim 𝒱(ℱ) ≥ aff dim{b(γ) : γ ∈ ℱ} + 1 on every semidefinite face, conv(𝒟) = 𝒟_SDP and Opt = Opt_SDP
-- statement:
--   Consider the QCQP (1) with $m\ge1$ constraints, its epigraph $\mathcal D$ and the projected epigraph $\mathcal D_{\mathrm{SDP}}$ of its standard SDP relaxation. Suppose Assumption 1 (primal feasibility and some $\gamma^*\in\mathbb R^m$, nonnegative on the inequality constraints, with $A(\gamma^*)\succ0$) and Assumption 3 ($\Gamma$ is polyhedral) hold. Suppose furthermore that every semidefinite face $\mathcal F$ of $\Gamma$ satisfies
--   $$\dim\mathcal V(\mathcal F)\ \ge\ \operatorname{aff\,dim}\{b(\gamma):\gamma\in\mathcal F\}+1 .$$
--   Then
--   $$\mathrm{conv}(\mathcal D)=\mathcal D_{\mathrm{SDP}}\qquad\text{and}\qquad\mathrm{Opt}=\mathrm{Opt}_{\mathrm{SDP}}.$$
--
--   This is the main convex hull result of §4: under the stated conditions the Shor relaxation describes the convex hull of the epigraph exactly, and in particular its value equals the QCQP's value.
--
--   **Formalization Note.** Constraints are indexed by $i\in\{0,\dots,m-1\}$ (`Fin m`), constraint $i$ being the paper's constraint $i+1$; it is an inequality exactly when $i<m_I$. Faces are nonempty (the empty face imposes nothing under the page's convention $\operatorname{aff\,dim}\emptyset=-1$). $\mathrm{Opt}$ and $\mathrm{Opt}_{\mathrm{SDP}}$ are infima in `EReal`. The hypotheses are exactly those of the page together with the paper's standing assumption $m\ge1$ (p. 1); Assumption 2 is not assumed, since it follows from Assumption 3.
-- source:
--   arXiv:1911.09195v3, Theorem 1, p. 13

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP
import Definitions.Def_QCQPTightness_ConvHull_Faces

namespace QCQPTightness.ConvHull

/-- Theorem 1 (arXiv:1911.09195v3, p. 13). Suppose `m ≥ 1`, Assumptions 1 and 3 hold, and every
semidefinite face `ℱ` of `Γ` has `dim 𝒱(ℱ) ≥ aff dim {b(γ) : γ ∈ ℱ} + 1`. Then
`conv(𝒟) = 𝒟_SDP` and `Opt = Opt_SDP`. -/
theorem theorem_1 {N m : ℕ} (P : QCQP N m) (hm : 1 ≤ m)
    (h1 : P.Assumption1) (h3 : P.Assumption3)
    (hdim : ∀ F, P.IsSemidefiniteFace F →
      affdim (P.bγ '' F) + 1 ≤ Module.finrank ℝ (P.V F)) :
    convexHull ℝ P.D = P.DSDP ∧ P.Opt = P.OptSDP := by sorry

end QCQPTightness.ConvHull

-- Prove2me | Theorems.Thm_QCQPTightness_ConvHull_lemma_4
-- name    : QCQPTightness.ConvHull.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:28:05.703065+00:00
-- url     : https://prove2.me/theorems/a3271f4e-2c31-423a-b7e4-5ff41c50bbda
-- title:
--   Lemma 4, p. 10 — under Assumptions 1, 2 and the convex decomposition condition (7), conv(𝒟) = 𝒟_SDP and Opt = Opt_SDP
-- statement:
--   Suppose Assumptions 1 and 2 hold, and suppose the decomposition condition
--
--   **(7)** for every $(\hat x,\hat t)\in\mathcal D_{\mathrm{SDP}}$ with $\mathcal F(\hat x)$ semidefinite, $(\hat x,\hat t)$ is a convex combination of points $(x_\alpha,t_\alpha)\in\mathcal D_{\mathrm{SDP}}$ with $\operatorname{aff\,dim}\mathcal F(x_\alpha)>\operatorname{aff\,dim}\mathcal F(\hat x)$.
--
--   Then
--   $$\mathrm{conv}(\mathcal D)=\mathcal D_{\mathrm{SDP}}\qquad\text{and}\qquad \mathrm{Opt}=\mathrm{Opt}_{\mathrm{SDP}}.$$
--
--   This reduces the convex hull question to a local decomposition step, which Lemma 7 supplies when $\Gamma$ is polyhedral.
--
--   **Formalization Note.** "A convex combination of points $(x_\alpha,t_\alpha)\in\mathcal D_{\mathrm{SDP}}$ with $\operatorname{aff\,dim}\mathcal F(x_\alpha)>\operatorname{aff\,dim}\mathcal F(\hat x)$" is membership in the convex hull of the set of all such points (finite convex combinations are exactly the convex hull). Values are compared in `EReal`. The standing assumption $m\ge1$ is not needed and is omitted.
-- source:
--   arXiv:1911.09195v3, Lemma 4 and condition (7), p. 10

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP
import Definitions.Def_QCQPTightness_ConvHull_Faces

namespace QCQPTightness.ConvHull

/-- Lemma 4 (arXiv:1911.09195v3, p. 10). Under Assumptions 1 and 2 and condition (7) — every
`(x̂, t̂) ∈ 𝒟_SDP` with `ℱ(x̂)` semidefinite is a convex combination of points `(x_α, t_α) ∈ 𝒟_SDP`
with `aff dim ℱ(x_α) > aff dim ℱ(x̂)` — we have `conv(𝒟) = 𝒟_SDP` and `Opt = Opt_SDP`. -/
theorem lemma_4 {N m : ℕ} (P : QCQP N m) (h1 : P.Assumption1) (h2 : P.Assumption2)
    (h7 : ∀ p ∈ P.DSDP, P.IsSemidefiniteFace (P.faceOf p.1) →
      p ∈ convexHull ℝ {p' ∈ P.DSDP | affdim (P.faceOf p.1) < affdim (P.faceOf p'.1)}) :
    convexHull ℝ P.D = P.DSDP ∧ P.Opt = P.OptSDP := by sorry

end QCQPTightness.ConvHull

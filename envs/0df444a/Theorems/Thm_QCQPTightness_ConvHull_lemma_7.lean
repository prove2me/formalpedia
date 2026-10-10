-- Prove2me | Theorems.Thm_QCQPTightness_ConvHull_lemma_7
-- name    : QCQPTightness.ConvHull.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:56.468439+00:00
-- url     : https://prove2.me/theorems/327031df-4da5-4c26-99e6-714b1dfb4525
-- title:
--   Lemma 7, p. 13 — under Assumptions 1, 3 and dim 𝒱(ℱ) ≥ aff dim{b(γ) : γ ∈ ℱ} + 1, a point of 𝒟_SDP with semidefinite ℱ(x̂) splits into points with larger aff dim ℱ
-- statement:
--   Suppose Assumptions 1 and 3 hold, and that every semidefinite face $\mathcal F$ of $\Gamma$ satisfies
--   $$\dim\mathcal V(\mathcal F)\ \ge\ \operatorname{aff\,dim}\{b(\gamma):\gamma\in\mathcal F\}+1 .$$
--   Let $(\hat x,\hat t)\in\mathcal D_{\mathrm{SDP}}$ with $\mathcal F(\hat x)$ a semidefinite face of $\Gamma$. Then $(\hat x,\hat t)$ is a convex combination of points $(x_\alpha,t_\alpha)\in\mathcal D_{\mathrm{SDP}}$ with
--   $$\operatorname{aff\,dim}\mathcal F(x_\alpha)>\operatorname{aff\,dim}\mathcal F(\hat x).$$
--
--   This is condition (7) of Lemma 4 for polyhedral $\Gamma$, and the main technical step of the convex hull theorem.
--
--   **Formalization Note.** "A convex combination of points …" is membership in the convex hull of the set of all such points. Faces are nonempty; $\dim\mathcal V(\mathcal F)$ is the rank of the subspace and $\operatorname{aff\,dim}$ the dimension of the direction of the affine span. The standing assumption $m\ge1$ is not needed and is omitted.
-- source:
--   arXiv:1911.09195v3, Lemma 7, p. 13

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP
import Definitions.Def_QCQPTightness_ConvHull_Faces

namespace QCQPTightness.ConvHull

/-- Lemma 7 (arXiv:1911.09195v3, p. 13). Under Assumptions 1 and 3, and if every semidefinite
face `ℱ` of `Γ` has `dim 𝒱(ℱ) ≥ aff dim {b(γ) : γ ∈ ℱ} + 1`: a point `(x̂, t̂) ∈ 𝒟_SDP` whose face
`ℱ(x̂)` is semidefinite is a convex combination of points `(x_α, t_α) ∈ 𝒟_SDP` with
`aff dim ℱ(x_α) > aff dim ℱ(x̂)`. -/
theorem lemma_7 {N m : ℕ} (P : QCQP N m) (h1 : P.Assumption1) (h3 : P.Assumption3)
    (hdim : ∀ F, P.IsSemidefiniteFace F →
      affdim (P.bγ '' F) + 1 ≤ Module.finrank ℝ (P.V F))
    (p : (Fin N → ℝ) × ℝ) (hp : p ∈ P.DSDP) (hF : P.IsSemidefiniteFace (P.faceOf p.1)) :
    p ∈ convexHull ℝ {p' ∈ P.DSDP | affdim (P.faceOf p.1) < affdim (P.faceOf p'.1)} := by sorry

end QCQPTightness.ConvHull

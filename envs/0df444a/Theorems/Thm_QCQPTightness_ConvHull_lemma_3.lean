-- Prove2me | Theorems.Thm_QCQPTightness_ConvHull_lemma_3
-- name    : QCQPTightness.ConvHull.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:28:13.340181+00:00
-- url     : https://prove2.me/theorems/ffadeacc-7ca0-45c9-b80c-05d104cc225d
-- title:
--   Lemma 3, p. 9 — under Assumptions 1 and 2, a point (x̂, t̂) ∈ 𝒟_SDP whose face ℱ(x̂) is definite lies in 𝒟
-- statement:
--   Suppose Assumptions 1 and 2 hold. Let $(\hat x,\hat t)\in\mathcal D_{\mathrm{SDP}}$ and let $\mathcal F(\hat x)=\arg\max_{\gamma\in\Gamma}q(\gamma,\hat x)$. If $\mathcal F(\hat x)$ is a definite face of $\Gamma$ (it contains some $\gamma$ with $A(\gamma)\succ0$), then
--   $$(\hat x,\hat t)\in\mathcal D,$$
--   that is, $\hat x$ is feasible for the QCQP and $q_0(\hat x)\le2\hat t$.
--
--   This is the "easy part" of the framework: only points whose face is semidefinite can lie outside the true epigraph.
--
--   **Formalization Note.** Constraints are indexed by $i\in\{0,\dots,m-1\}$ (`Fin m`), constraint $i$ being the paper's constraint $i+1$; it is an inequality exactly when $i<m_I$. The standing assumption $m\ge1$ is not needed and is omitted.
-- source:
--   arXiv:1911.09195v3, Lemma 3, p. 9

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP
import Definitions.Def_QCQPTightness_ConvHull_Faces

namespace QCQPTightness.ConvHull

/-- Lemma 3 (arXiv:1911.09195v3, p. 9). Under Assumptions 1 and 2, a point `(x̂, t̂) ∈ 𝒟_SDP`
whose face `ℱ(x̂)` is definite lies in `𝒟`. -/
theorem lemma_3 {N m : ℕ} (P : QCQP N m) (h1 : P.Assumption1) (h2 : P.Assumption2)
    (p : (Fin N → ℝ) × ℝ) (hp : p ∈ P.DSDP) (hF : P.IsDefiniteFace (P.faceOf p.1)) :
    p ∈ P.D := by sorry

end QCQPTightness.ConvHull

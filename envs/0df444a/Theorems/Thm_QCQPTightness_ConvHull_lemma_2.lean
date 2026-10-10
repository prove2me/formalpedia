-- Prove2me | Theorems.Thm_QCQPTightness_ConvHull_lemma_2
-- name    : QCQPTightness.ConvHull.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:49.474053+00:00
-- url     : https://prove2.me/theorems/c672a31d-56d7-4566-810d-4b0774aac1ea
-- title:
--   Lemma 2, p. 9 — the shared zero eigenspace 𝒱(ℱ) of a semidefinite face ℱ of Γ meets the unit sphere 𝐒^{N−1}
-- statement:
--   Let $\mathcal F$ be a semidefinite face of $\Gamma$, i.e. a face on which no $A(\gamma)$ is positive definite. Then its shared zero eigenspace
--   $$\mathcal V(\mathcal F)=\{v\in\mathbb R^N:\ A(\gamma)v=0\ \ \forall\gamma\in\mathcal F\}$$
--   contains a unit vector: $\mathcal V(\mathcal F)\cap\mathbb S^{N-1}\neq\emptyset$.
--
--   So, although each $A(\gamma)$ on the face is merely singular, the matrices of a semidefinite face share a common null vector. This is the direction along which the convex decomposition of Lemma 7 moves.
--
--   **Formalization Note.** The unit sphere is expressed with the Euclidean inner product, $v^\top v=1$ (the default norm on `Fin N → ℝ` is the sup norm). No assumption is needed.
-- source:
--   arXiv:1911.09195v3, Lemma 2, p. 9

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP
import Definitions.Def_QCQPTightness_ConvHull_Faces

namespace QCQPTightness.ConvHull

/-- Lemma 2 (arXiv:1911.09195v3, p. 9). If `ℱ` is a semidefinite face of `Γ`, then the shared
zero eigenspace `𝒱(ℱ)` meets the Euclidean unit sphere `𝐒^{N−1}`. -/
theorem lemma_2 {N m : ℕ} (P : QCQP N m) (F : Set (Fin m → ℝ))
    (hF : P.IsSemidefiniteFace F) :
    ∃ v ∈ P.V F, v ⬝ᵥ v = 1 := by sorry

end QCQPTightness.ConvHull

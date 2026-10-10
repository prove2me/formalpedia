-- Prove2me | Theorems.Thm_QCQPTightness_ConvHull_observation_1
-- name    : QCQPTightness.ConvHull.observation_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:28:12.030293+00:00
-- url     : https://prove2.me/theorems/673ec5ce-d400-4708-bc32-2bce074babda
-- title:
--   Observation 1, p. 10 — under Assumption 1, a face ℱ of Γ with aff dim(ℱ) = m is definite
-- statement:
--   Suppose Assumption 1 holds and let $\mathcal F$ be a face of $\Gamma\subseteq\mathbb R^m$. If
--   $$\operatorname{aff\,dim}(\mathcal F)=m,$$
--   then $\mathcal F$ is a definite face: some $\gamma\in\mathcal F$ has $A(\gamma)\succ0$.
--
--   Together with Lemma 3, this makes $\operatorname{aff\,dim}\mathcal F(\hat x)$ a progress measure bounded by $m$: a point whose face reaches full dimension already lies in $\mathcal D$.
--
--   **Formalization Note.** Faces are nonempty by definition; the affine dimension is the dimension of the direction of the affine span. The standing assumption $m\ge1$ is not needed and is omitted.
-- source:
--   arXiv:1911.09195v3, Observation 1, p. 10

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP
import Definitions.Def_QCQPTightness_ConvHull_Faces

namespace QCQPTightness.ConvHull

/-- Observation 1 (arXiv:1911.09195v3, p. 10). Under Assumption 1, a face `ℱ` of `Γ` with
`aff dim(ℱ) = m` is definite. -/
theorem observation_1 {N m : ℕ} (P : QCQP N m) (h1 : P.Assumption1)
    (F : Set (Fin m → ℝ)) (hF : P.IsFace F) (hdim : affdim F = m) :
    P.IsDefiniteFace F := by sorry

end QCQPTightness.ConvHull

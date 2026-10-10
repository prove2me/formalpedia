-- Prove2me | Theorems.Thm_QCQPTightness_Exact_lemma_2
-- name    : QCQPTightness.Exact.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:21:25.484565+00:00
-- url     : https://prove2.me/theorems/9c177225-d0ae-4ac6-a8fb-2be777aa53ef
-- title:
--   Lemma 2, p. 9 — a semidefinite face ℱ has 𝒱(ℱ) ∩ 𝐒^{N−1} ≠ ∅
-- statement:
--   Let $\mathcal F$ be a semidefinite face of $\Gamma$: a face on which no $A(\gamma)$ is positive definite. Then the shared zero eigenspace contains a unit vector:
--
--   $$\mathcal V(\mathcal F)\cap\mathbf S^{N-1}\neq\emptyset,\qquad\text{i.e. there is } v\in\mathbb R^N,\ v^\top v=1,\ A(\gamma)v=0\ \ \forall\gamma\in\mathcal F.$$
--
--   A priori each $A(\gamma)$, $\gamma\in\mathcal F$, is singular; the lemma says they share a common null vector. This nonzero vector is the direction along which the proof of Theorem 3 moves an SDP optimizer.
--
--   **Formalization Note** The unit sphere is written $v\cdot v=1$, because the norm on `Fin N → ℝ` is the sup norm. The lemma has no other hypotheses.
-- source:
--   arXiv:1911.09195v3, Lemma 2, p. 9

import Mathlib
import Definitions.Def_QCQPTightness_Exact_QCQP
import Definitions.Def_QCQPTightness_Exact_Faces

namespace QCQPTightness.Exact
theorem lemma_2 {N m : ℕ} (P : QCQP N m) (F : Set (Fin m → ℝ))
    (hF : P.IsSemidefiniteFace F) :
    ∃ v ∈ P.V F, v ⬝ᵥ v = 1 := by sorry
end QCQPTightness.Exact

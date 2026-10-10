-- Prove2me | Theorems.Thm_QCQPTightness_Exact_separation_step
-- name    : QCQPTightness.Exact.separation_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:24:15.694297+00:00
-- url     : https://prove2.me/theorems/152915be-0cc1-459b-a07c-458682e496c4
-- title:
--   §5, proof of Theorem 3, p. 24, separation step — v ∈ 𝒱(ℱ) ∖ {0}, ε > 0 with vᵀb(γ) ≤ −ε on ℱ
-- statement:
--   Suppose $\Gamma$ is polyhedral (Assumption 3). Let $\mathcal F$ be a semidefinite face of $\Gamma$ with
--
--   $$0\notin\mathrm{Proj}_{\mathcal V(\mathcal F)}\{b(\gamma):\gamma\in\mathcal F\}.$$
--
--   Then there are a nonzero $v\in\mathcal V(\mathcal F)$ and $\epsilon>0$ such that
--
--   $$v^\top b(\gamma)\le-\epsilon\qquad\text{for all }\gamma\in\mathcal F.$$
--
--   This is the separation step of the proof of Theorem 3. It produces the direction $(v,-\epsilon)$ along which an SDP optimizer with a semidefinite face could be moved to a strictly smaller value of $t$.
-- source:
--   arXiv:1911.09195v3, §5, proof of Theorem 3, p. 24, separation step

import Mathlib
import Definitions.Def_QCQPTightness_Exact_QCQP
import Definitions.Def_QCQPTightness_Exact_Faces
import Definitions.Def_QCQPTightness_Exact_Proj

namespace QCQPTightness.Exact
theorem separation_step {N m : ℕ} (P : QCQP N m) (h3 : P.Assumption3)
    (F : Set (Fin m → ℝ)) (hF : P.IsSemidefiniteFace F)
    (h0 : (0 : EuclideanSpace ℝ (Fin N)) ∉ projB P F) :
    ∃ v ∈ P.V F, v ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ γ ∈ F, P.bγ γ ⬝ᵥ v ≤ -ε := by sorry
end QCQPTightness.Exact

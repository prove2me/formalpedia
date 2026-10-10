-- Prove2me | Theorems.Thm_QCQPTightness_Exact_theorem_3
-- name    : QCQPTightness.Exact.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:21:38.869811+00:00
-- url     : https://prove2.me/theorems/56b74f62-d317-483a-8bdc-e3f895645d0f
-- title:
--   Theorem 3, p. 23 — polyhedral Γ and 0 ∉ Proj_{𝒱(ℱ)}{b(γ) : γ ∈ ℱ} on semidefinite faces: SDP optimizers lie in 𝒟, Opt = Opt_SDP
-- statement:
--   Consider a QCQP with $m\ge1$ constraints and suppose:
--
--   1. Assumption 1: the QCQP is feasible and some $\gamma^*$ with $\gamma^*_i\ge 0$ for $i\in[\![m_I]\!]$ has $A(\gamma^*)\succ 0$;
--   2. Assumption 3: $\Gamma$ is polyhedral;
--   3. for every semidefinite face $\mathcal F$ of $\Gamma$,
--   $$0\notin\mathrm{Proj}_{\mathcal V(\mathcal F)}\{b(\gamma):\gamma\in\mathcal F\}.$$
--
--   Then every optimizer $(x^*,t^*)\in\arg\min_{(x,t)\in\mathcal D_{\mathrm{SDP}}}2t$ satisfies $(x^*,t^*)\in\mathcal D$. In particular,
--
--   $$\mathrm{Opt}=\mathrm{Opt}_{\mathrm{SDP}}.$$
--
--   So under these conditions the SDP relaxation is exact, and the $x$-block of any optimal lifted matrix of the SDP is an optimal solution of the QCQP.
--
--   **Formalization Note** "$(x^*,t^*)\in\arg\min 2t$" is stated as membership in $\mathcal D_{\mathrm{SDP}}$ together with $2t^*\le 2t$ for every $(x,t)\in\mathcal D_{\mathrm{SDP}}$. Existence of an optimizer is not assumed, and the value identity is stated as a separate conclusion in `EReal`. The standing assumption $m\ge 1$ of the paper (p. 1) is a hypothesis. Faces are nonempty, and the projection is the Euclidean orthogonal projection.
-- source:
--   arXiv:1911.09195v3, Theorem 3, p. 23

import Mathlib
import Definitions.Def_QCQPTightness_Exact_QCQP
import Definitions.Def_QCQPTightness_Exact_Faces
import Definitions.Def_QCQPTightness_Exact_Proj

namespace QCQPTightness.Exact
theorem theorem_3 {N m : ℕ} (P : QCQP N m) (hm : 1 ≤ m) (h1 : P.Assumption1)
    (h3 : P.Assumption3)
    (hproj : ∀ F, P.IsSemidefiniteFace F → (0 : EuclideanSpace ℝ (Fin N)) ∉ projB P F) :
    (∀ p ∈ P.DSDP, (∀ p' ∈ P.DSDP, 2 * p.2 ≤ 2 * p'.2) → p ∈ P.D) ∧ P.Opt = P.OptSDP := by sorry
end QCQPTightness.Exact

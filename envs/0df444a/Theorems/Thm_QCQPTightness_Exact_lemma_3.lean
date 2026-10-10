-- Prove2me | Theorems.Thm_QCQPTightness_Exact_lemma_3
-- name    : QCQPTightness.Exact.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:20:40.552008+00:00
-- url     : https://prove2.me/theorems/e7507378-3e72-40e9-8711-25e4e0df3f73
-- title:
--   Lemma 3, p. 9 — under Assumptions 1–2, (x̂, t̂) ∈ 𝒟_SDP with ℱ(x̂) definite lies in 𝒟
-- statement:
--   Suppose Assumptions 1 and 2 hold, and let $(\hat x,\hat t)\in\mathcal D_{\mathrm{SDP}}$. If the face $\mathcal F(\hat x)=\arg\max_{\gamma\in\Gamma}q(\gamma,\hat x)$ is a definite face of $\Gamma$, then
--
--   $$(\hat x,\hat t)\in\mathcal D,$$
--
--   that is, $\hat x$ is feasible for the QCQP and $q_0(\hat x)\le 2\hat t$.
--
--   This is the "easy part" of the paper's framework. Every exactness argument reduces to showing that the relevant face is definite.
--
--   **Formalization Note** The hypothesis that $\mathcal F(\hat x)$ is a definite face includes that it is a nonempty face of $\Gamma$.
-- source:
--   arXiv:1911.09195v3, Lemma 3, p. 9

import Mathlib
import Definitions.Def_QCQPTightness_Exact_QCQP
import Definitions.Def_QCQPTightness_Exact_Faces

namespace QCQPTightness.Exact
theorem lemma_3 {N m : ℕ} (P : QCQP N m) (h1 : P.Assumption1) (h2 : P.Assumption2)
    (p : (Fin N → ℝ) × ℝ) (hp : p ∈ P.DSDP) (hdef : P.IsDefiniteFace (P.faceOf p.1)) :
    p ∈ P.D := by sorry
end QCQPTightness.Exact

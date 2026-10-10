-- Prove2me | Theorems.Thm_QCQPTightness_Exact_lemma_8
-- name    : QCQPTightness.Exact.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:20:57.205379+00:00
-- url     : https://prove2.me/theorems/0b467be1-c3e8-4815-8ebe-aa912c6ba140
-- title:
--   Lemma 8, p. 13 — Γ = Γ_e + cone(Γ_r) and ℱ(x̂) = ℱ_e(x̂) + cone(ℱ_r(x̂)) for polyhedral Γ
-- statement:
--   Suppose Assumption 3 holds ($\Gamma$ is polyhedral). Then there are polytopes $\Gamma_e=\mathrm{conv}(E)$ and $\Gamma_r=\mathrm{conv}(R)$, with $E,R\subseteq\mathbb R^m$ finite, such that
--
--   $$\Gamma=\Gamma_e+\mathrm{cone}(\Gamma_r).$$
--
--   Here $\Gamma_r$ may be trivial. Moreover, for every $\hat x\in\mathbb R^N$ for which $\sup_{\gamma\in\Gamma}q(\gamma,\hat x)$ is finite,
--
--   $$\mathcal F(\hat x)=\mathcal F_e(\hat x)+\mathrm{cone}(\mathcal F_r(\hat x)),$$
--
--   where $\mathcal F_e(\hat x)=\arg\max_{\gamma\in\Gamma_e}q(\gamma,\hat x)$ and $\mathcal F_r(\hat x)=\{\gamma\in\Gamma_r : \breve q(\gamma,\hat x)=0\}$.
--
--   The decomposition reduces statements about $\Gamma$ to finitely many extreme points and extreme rays. The proof of Theorem 3 uses this finiteness to choose its step size.
--
--   **Formalization Note** $\mathrm{cone}(S)$ is the conic hull (`PointedCone.hull`), which contains $0$, and $+$ is the Minkowski sum. "$\sup$ finite" is the bounded-above condition on $\{q(\gamma,\hat x):\gamma\in\Gamma\}$. The page prints "$\mathcal F_r(\hat x)$ is the face of $\Gamma_e$ satisfying $\breve q(\gamma,\hat x)=0$". The proof and its uses (Lemma 7, Theorem 3) decompose $\mathcal F_r\subseteq\Gamma_r$, so the formalization takes the face of $\Gamma_r$. This corrects a printed slip.
-- source:
--   arXiv:1911.09195v3, Lemma 8, p. 13

import Mathlib
import Definitions.Def_QCQPTightness_Exact_QCQP
import Definitions.Def_QCQPTightness_Exact_Faces
import Definitions.Def_QCQPTightness_Exact_Recession
open Pointwise

namespace QCQPTightness.Exact
theorem lemma_8 {N m : ℕ} (P : QCQP N m) (h3 : P.Assumption3) :
    ∃ E R : Finset (Fin m → ℝ),
      P.Gamma = convexHull ℝ (E : Set (Fin m → ℝ)) +
        (PointedCone.hull ℝ (convexHull ℝ (R : Set (Fin m → ℝ))) : Set (Fin m → ℝ)) ∧
      ∀ x : Fin N → ℝ, BddAbove ((fun γ => P.qγ γ x) '' P.Gamma) →
        P.faceOf x =
          {γ | γ ∈ convexHull ℝ (E : Set (Fin m → ℝ)) ∧
              ∀ γ' ∈ convexHull ℝ (E : Set (Fin m → ℝ)), P.qγ γ' x ≤ P.qγ γ x} +
            (PointedCone.hull ℝ
              {γ | γ ∈ convexHull ℝ (R : Set (Fin m → ℝ)) ∧ qBreve P γ x = 0} :
              Set (Fin m → ℝ)) := by sorry
end QCQPTightness.Exact

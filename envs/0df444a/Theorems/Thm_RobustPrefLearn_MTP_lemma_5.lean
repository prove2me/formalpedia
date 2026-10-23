-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_lemma_5
-- name    : RobustPrefLearn.MTP.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:03.162962+00:00
-- url     : https://prove2.me/theorems/8fe407d2-7bf2-4531-9dd4-3c0d74601d8b
-- title:
--   Lemma 5, p. 58 — the per-set minimizer of D_S over M_p(σ*) × M_p(σ̂_k) is the OA pair
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$. Let $k\in\{2,\dots,K\}$ and $S\in\mathcal S$. The problem
--   $$\min_{f\in\mathcal M_p(\sigma_*)}\ \min_{\bar f\in\mathcal M_p(\hat\sigma_k)} D_S(f\|\bar f)$$
--   is solved by $f^*=f^{\mathrm{OA}}_{\sigma_*}$ and $\bar f^*=f^{\mathrm{OA}}_{\hat\sigma_k}$: both are feasible, and $D_S(f^{\mathrm{OA}}_{\sigma_*}\|f^{\mathrm{OA}}_{\hat\sigma_k})\le D_S(f\|\bar f)$ for all feasible $f,\bar f$.
--
--   Because the minimizer does not depend on $S$ or $k$, the OA preference is the hardest instance simultaneously for every display set.
--
--   **Formalization Note** Versions $1,\dots,K$ are `Fin K` (version $m$ is `⟨m-1, _⟩`), and a ranking `σ : Equiv.Perm (Fin K)` sends a version to its rank **0-based**, so `σ X = 0` is the paper's $\sigma(X)=1$. The paper's $k\in\{2,\dots,K\}$ is `1 ≤ k.val`. The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 58, Lemma 5, (47)

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA

open scoped ENNReal

namespace RobustPrefLearn.MTP

/-- Lemma 5, p. 58. For any version `k ∈ {2, …, K}` (0-based `k.val ≥ 1`) and any display set
`S`, the problem `min_{f ∈ M_p(σ*)} min_{f̄ ∈ M_p(σ̂_k)} D_S(f‖f̄)` is solved by
`f* = f^OA_{σ*}` and `f̄* = f^OA_{σ̂_k}`. -/
theorem lemma_5 (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (k : Fin K)
    (hk : 1 ≤ k.val) (S : DS K) :
    oa p (1 : Equiv.Perm (Fin K)) ∈ MpRank p (1 : Equiv.Perm (Fin K)) ∧
    oa p (sigmaHat k) ∈ MpRank p (sigmaHat k) ∧
    ∀ f ∈ MpRank p (1 : Equiv.Perm (Fin K)), ∀ g ∈ MpRank p (sigmaHat k),
      DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p (sigmaHat k)) S ≤ DS_ f g S := by sorry

end RobustPrefLearn.MTP

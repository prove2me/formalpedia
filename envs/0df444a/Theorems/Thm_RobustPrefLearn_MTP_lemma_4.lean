-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_lemma_4
-- name    : RobustPrefLearn.MTP.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:11.856363+00:00
-- url     : https://prove2.me/theorems/80264de6-8dd4-400d-9c64-f3c255843aa1
-- title:
--   Lemma 4, p. 58 — dominance by σ̂_k: f̂ ∈ M_p(σ̂_k) beats any f ∈ M_p(σ_k) for every λ
-- statement:
--   Let $\sigma_*$ be the identity ranking and, for a version $k$, let $\Sigma_k$ be the rankings with $\sigma(k)=1$. Throughout, $K\ge2$ versions and $0<p<1$.
--
--   For every $f^*\in\mathcal M_p(\sigma_*)$, every $\sigma_k\in\Sigma_k$ and every $f\in\mathcal M_p(\sigma_k)$ there is $\hat f\in\mathcal M_p(\hat\sigma_k)$ such that for every $\lambda\in\Delta(\mathcal S)$,
--   $$D_\lambda(f^*\|\hat f)\le D_\lambda(f^*\|f).$$
--
--   The point is that $\hat f$ is chosen before $\lambda$. The lemma reduces the inner minimization over all alternatives with top version $k$ to the single ranking $\hat\sigma_k$.
--
--   **Formalization Note** Versions $1,\dots,K$ are `Fin K` (version $m$ is `⟨m-1, _⟩`), and a ranking `σ : Equiv.Perm (Fin K)` sends a version to its rank **0-based**, so `σ X = 0` is the paper's $\sigma(X)=1$. The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 58, Lemma 4

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA

open scoped ENNReal

namespace RobustPrefLearn.MTP

/-- Lemma 4, p. 58. For any `f* ∈ M_p(σ*)` (`σ*` the identity ranking), any ranking `σ_k` with
`σ_k(k) = 1` and any `f ∈ M_p(σ_k)`, there is `f̂ ∈ M_p(σ̂_k)` such that
`D_λ(f*‖f̂) ≤ D_λ(f*‖f)` for every `λ ∈ Δ(𝒮)`. -/
theorem lemma_4 (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (k : Fin K)
    (fstar : Pref K) (hfstar : fstar ∈ MpRank p (1 : Equiv.Perm (Fin K)))
    (σk : Equiv.Perm (Fin K)) (hσk : (σk k).val = 0)
    (f : Pref K) (hf : f ∈ MpRank p σk) :
    ∃ fh ∈ MpRank p (sigmaHat k), ∀ lam ∈ simplex K, Dlam lam fstar fh ≤ Dlam lam fstar f := by sorry

end RobustPrefLearn.MTP

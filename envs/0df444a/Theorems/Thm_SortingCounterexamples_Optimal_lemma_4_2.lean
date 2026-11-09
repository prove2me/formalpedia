-- Prove2me | Theorems.Thm_SortingCounterexamples_Optimal_lemma_4_2
-- name    : SortingCounterexamples.Optimal.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:39.668788+00:00
-- url     : https://prove2.me/theorems/9e9bc87d-ddeb-4945-a7c5-d9683542544a
-- title:
--   Lemma 4.2 — every weight $w_t$ of the update is log-concave on $[0,1]^n$
-- statement:
--   Fix $\gamma>0$. Let $w_t$ be the weight after any $t$ rounds of the update (1), $w_0\equiv1$ and $w_{t+1}(x)=w_t(x)e^{-\ell_t(x)}$ with $\ell_t(x)=(1+\gamma n(x_j-x_i))_+$ for the pair $\{i,j\}$ returned on round $t$, oriented so that the round's query places $i$ before $j$. Then $w_t\ge0$ on $[0,1]^n$ and
--   $$w_t(\lambda x+(1-\lambda)y)\ \ge\ w_t(x)^{\lambda}\,w_t(y)^{1-\lambda}\qquad\text{for all }x,y\in[0,1]^n,\ \lambda\in[0,1].$$
--
--   This is the property that lets Grünbaum's inequality (Theorem 4.1) be applied to the normalized weight in Lemma 4.3.
--
--   **Formalization Note** Log-concavity is the published platform definition `ConvexOptimization.LogConcaveOn` (power form, zeros allowed). The statement holds for every transcript, whatever the queries were.
--
--   Differences from the source:
--   - generalization: one universal constant γ > 0, fixed sufficiently large → every γ > 0; reason: the statement holds for each γ > 0, so it specializes to the source's fixed γ
--   - generalization: w_t produced by the algorithm, whose queries sort the barycenters → w_t after an arbitrary transcript of queries and returned pairs; reason: every run of the algorithm (any tie-breaking, any oracle) is such a transcript
-- source:
--   Noga Alon, Shay Moran, Shlomo Moran, STOC 2027 submission #549 (October 2026), printed p. 16 / PDF p. 17, Lemma 4.2

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_SortingCounterexamples_Optimal_WeightedUpdate

namespace SortingCounterexamples.Optimal

/-- Lemma 4.2: for every transcript of queries and returned counterexamples, the weight `w_t`
produced by the update (1) is log-concave on `[0,1]^n`. -/
theorem lemma_4_2 {n : ℕ} (γ : ℝ) (hγ : 0 < γ) (h : Transcript n) :
    ConvexOptimization.LogConcaveOn (cube n) (weightAfter γ h) := by sorry

end SortingCounterexamples.Optimal

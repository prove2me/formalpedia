-- Prove2me | Theorems.Thm_SortingCounterexamples_Optimal_lemma_4_3
-- name    : SortingCounterexamples.Optimal.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:46.007687+00:00
-- url     : https://prove2.me/theorems/4a679ccb-5c90-43a7-88bd-8f0c37867f85
-- title:
--   Lemma 4.3 — $W_{t+1}\le\rho W_t$ for a universal $\rho<1$ whenever a counterexample is returned
-- statement:
--   There is a universal constant $\rho<1$ with the following property. Let $\gamma>0$, let $w_t$ be the weight after any transcript, with total mass $W_t=\int_{[0,1]^n}w_t$ and barycenter $c_t$ of $w_t/W_t$ on the cube, and let the query $\pi$ be a ranking that sorts the coordinates of $c_t$ (ties broken arbitrarily). If a counterexample $\{i,j\}$ is returned and $w_{t+1}=w_t e^{-\ell_t}$ is the updated weight, then
--   $$W_{t+1}\ \le\ \rho\,W_t .$$
--
--   This is the analogue of the weighted-majority progress bound; it gives $W_T\le\rho^T$ after $T$ counterexamples (equation (2)).
--
--   **Formalization Note** The proof's value is $\rho=1-(1-e^{-1})/e$, independent of $\gamma$, $n$ and the transcript; the Lean statement puts $\rho$ before $\gamma$ and every instance.
--
--   Differences from the source:
--   - generalization: one universal constant γ > 0, fixed sufficiently large → every γ > 0; reason: the statement holds for each γ > 0, so it specializes to the source's fixed γ
--   - generalization: the weighted algorithm's current weight w_t (all earlier queries sort the earlier barycenters) → the weight after an arbitrary earlier transcript; only the current query is required to sort the current barycenter; reason: every run of the algorithm, with any tie-breaking, satisfies the Lean hypotheses
-- source:
--   Noga Alon, Shay Moran, Shlomo Moran, STOC 2027 submission #549 (October 2026), printed p. 16 / PDF p. 17, Lemma 4.3 (proof to printed p. 17 / PDF p. 18)

import Mathlib
import Definitions.Def_SortingCounterexamples_Optimal_WeightedUpdate

namespace SortingCounterexamples.Optimal

/-- Lemma 4.3: there is a universal `ρ < 1` such that, whenever the query `π` sorts the
coordinates of the current barycenter (ties broken arbitrarily) and a counterexample `s` is
returned, the total mass satisfies `W_{t+1} ≤ ρ W_t`. -/
theorem lemma_4_3 :
    ∃ ρ : ℝ, ρ < 1 ∧ ∀ γ : ℝ, 0 < γ → ∀ {n : ℕ} (h : Transcript n) (π : Ranking n)
      (s : ItemPair n), SortsCoords (barycenter (weightAfter γ h)) π →
      mass (weightAfter γ (h ++ [(π, s)])) ≤ ρ * mass (weightAfter γ h) := by sorry

end SortingCounterexamples.Optimal

-- Prove2me | Theorems.Thm_RubinsteinNash_WeakNash_claim_8_2
-- name    : RubinsteinNash.WeakNash.claim_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:26.668527+00:00
-- url     : https://prove2.me/theorems/e09dc6cf-7ce3-4764-ab7d-be92f5d56ad8
-- title:
--   Claim 8.2, p. 50 — trimming moves each player's mixed strategy by at most 2/(k − 1) in L1
-- statement:
--   Let $x$ be a mixed-strategy profile of a finite game, let $\epsilon>0$ and $k>1$, and let $\hat x$ be the trimmed profile of the proof of Lemma 8.1 (each $\epsilon$-optimal player $v$ drops the actions more than $\epsilon k$ below $U^v_{\max}(x^{-v})$ and renormalises; every other player keeps $x^v$). Then for every player $v$,
--   $$\sum_{s\in S^v}\bigl|\hat x^v_s-x^v_s\bigr|\ \le\ \frac{2}{k-1}.$$
--
--   So when $k$ is large the trimmed profile is close to $x$ in every coordinate, which is what keeps the expected payoffs of all players nearly unchanged.
--
--   **Formalization Note.** The page states the claim for the players of the bipartite polymatrix game; it uses no polymatrix structure, so it is stated for an arbitrary finite game. For a player that is not $\epsilon$-optimal, $\hat x^v=x^v$ and the left side is $0$.
-- source:
--   Rubinstein, arXiv:1606.04550 (version dated August 26, 2016), Claim 8.2 (= [32, Claim 6]), §8.1, p. 50

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_RubinsteinNash_WeakNash_ApproxEquilibria

namespace RubinsteinNash.WeakNash

theorem claim_8_2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x)
    (ε k : ℝ) (hε : 0 < ε) (hk : 1 < k) :
    ∀ v : ι, ∑ s : S v, |weakTrim u x ε k v s - x v s| ≤ 2 / (k - 1) := by sorry

end RubinsteinNash.WeakNash

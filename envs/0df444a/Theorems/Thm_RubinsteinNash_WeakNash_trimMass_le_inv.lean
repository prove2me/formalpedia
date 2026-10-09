-- Prove2me | Theorems.Thm_RubinsteinNash_WeakNash_trimMass_le_inv
-- name    : RubinsteinNash.WeakNash.trimMass_le_inv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:35.003993+00:00
-- url     : https://prove2.me/theorems/af16d46c-b198-4f54-a796-5125d49c3b22
-- title:
--   Proof of Lemma 8.1, p. 50 — for an ε-optimal player and k > 1, the trimmed mass z^v is at most 1/k
-- statement:
--   Let $x$ be a mixed-strategy profile of a finite game, let $\epsilon>0$ and $k>1$, and let $v$ be a player whose mixed strategy $x^v$ is an $\epsilon$-best mixed response to $x^{-v}$. Let $z^v$ be the total probability that $x^v$ assigns to actions $s$ more than $\epsilon k$ away from the optimum, i.e. with $U^v_s(x^{-v})<U^v_{\max}(x^{-v})-\epsilon k$. Then
--   $$z^v\ \le\ \frac1k\ <\ 1 .$$
--
--   This is what makes the normalisation $x^v_s/(1-z^v)$ in the trimmed profile $\hat x$ well defined for the $\epsilon$-optimal players.
--
--   **Formalization Note.** The page says only that "$z^v$ is bounded away from 1"; the formalization states the quantitative bound $z^v\le 1/k$, which for $k>1$ is the bound away from 1. The statement uses no polymatrix structure, so it is stated for an arbitrary finite game, which contains the bipartite polymatrix games of Lemma 8.1.
-- source:
--   Rubinstein, arXiv:1606.04550 (version dated August 26, 2016), proof of Lemma 8.1, §8.1, p. 50 (sentence after the definition of x̂: 'for k > 1 and v who plays ϵ-optimally, z^v is bounded away from 1')

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_RubinsteinNash_WeakNash_ApproxEquilibria

namespace RubinsteinNash.WeakNash

theorem trimMass_le_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x)
    (ε k : ℝ) (hε : 0 < ε) (hk : 1 < k) (v : ι) (hv : IsEpsBestResponse u x ε v) :
    DGPNash.WellSupported.trimMass u x ε k v ≤ 1 / k := by sorry

end RubinsteinNash.WeakNash

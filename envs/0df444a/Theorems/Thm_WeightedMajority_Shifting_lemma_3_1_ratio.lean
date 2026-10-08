-- Prove2me | Theorems.Thm_WeightedMajority_Shifting_lemma_3_1_ratio
-- name    : WeightedMajority.Shifting.lemma_3_1_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:43:13.543905+00:00
-- url     : https://prove2.me/theorems/5a5d2f4a-daf4-4485-b075-44df0d1f0fc2
-- title:
--   §3, p. 224, proof of Lemma 3.1 — a mistake of WML multiplies the total weight by at most u = (1+β)/2 + (1−β)γ
-- statement:
--   Let $0 < \beta < 1$ and $0 \le \gamma < \tfrac12$, and consider a run of the algorithm WML with parameters $\beta, \gamma$ on a pool of $n$ algorithms and an arbitrary sequence of binary-labelled trials. Write $W^{(t)}$ for the total weight of the pool at the beginning of trial $t$. If the master algorithm makes a mistake in trial $t$, then
--   $$W^{(t+1)} \le \left(\frac{1+\beta}{2} + (1-\beta)\gamma\right) W^{(t)} .$$
--
--   This is the per-mistake contraction step of the proof of Lemma 3.1: members whose weight is at most $\gamma/n$ times the total are protected from the update, and their total weight is at most $\gamma W^{(t)}$, which is what the extra term $(1-\beta)\gamma$ accounts for. Since $\gamma < 1/2$, the factor is less than $1$.
--
--   **Formalization Note** $W^{(t)}$ is `totalWeight (w t)` and the factor is `uFactor β γ`. The run's initial weights are positive, as WML requires.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 224, Section 3, proof of Lemma 3.1

import Mathlib
import Definitions.Def_WeightedMajority_Shifting_WML

namespace WeightedMajority.Shifting

theorem lemma_3_1_ratio {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1 / 2)
    (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool)
    (hrun : IsWMLRun β γ x ρ w lam) (t : Fin T) (hmis : lam t ≠ ρ t) :
    totalWeight (w ((t : ℕ) + 1)) ≤ uFactor β γ * totalWeight (w t) := by sorry

end WeightedMajority.Shifting

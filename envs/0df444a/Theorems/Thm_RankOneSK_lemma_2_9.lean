-- Prove2me | Theorems.Thm_RankOneSK_lemma_2_9
-- name    : RankOneSK.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:28:45.323546+00:00
-- url     : https://prove2.me/theorems/d4ce1d19-c1bb-4219-a339-edb05c6c0bc0
-- title:
--   Lemma 2.9 — $\max_{i,j}|J_{ij}|\to0$ in probability for a β-GOE matrix
-- statement:
--   Let $\beta>0$ and let $J$ be an $n\times n$ β-GOE matrix: symmetric, $J_{ij}\sim\mathcal N(0,\beta^2/n)$ independent for $i<j$, and $J_{ii}=0$.
--
--   **Lemma 2.9.** $\max_{1\le i,j\le n}|J_{ij}|\to0$ in probability as $n\to\infty$: for every $t>0$,
--   $$\Pr\Big[\max_{1\le i,j\le n}|J_{ij}|>t\Big]\xrightarrow[n\to\infty]{}0 .$$
--
--   It lets Theorem 3.1 be applied to every pair of spins at once, since all entries are eventually below $j(d,\lambda,s)$.
--
--   Differences from the source:
--   - encoding: convergence in probability → for every t > 0, the probability that the deviation exceeds t tends to 0; reason: the definition of convergence in probability
--   - encoding: max_{i,j} |J_ij| > t → some entry |J_ik| > t; reason: equivalent; no max over an empty index set at n = 0
--   - encoding: J β-GOE: symmetric, J_ij iid N(0, β²/n) for i < j, J_ii = 0 → the published OAI.SKGap.disorderLaw β n on the entries above the diagonal, with coupling J the full symmetric zero-diagonal matrix; reason: the same law
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Lemma 2.9, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_SKHighTemperature

open OAI.SKGap MeasureTheory ProbabilityTheory Filter

namespace RankOneSK

/-- **Lemma 2.9.** Let `β > 0` and `J` be β-GOE. Then `max_{1⩽i,j⩽n} |J_ij| → 0` in probability.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Lemma 2.9, p.15.

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (±1 through `spinValue`), sites 0-based `Fin n`.
The β-GOE matrix `J` is the published `OAI.SKGap.Disorder n` under `disorderLaw β n`: entries
`J_ik`, `i < k`, i.i.d. `N(0, β²/n)`, `coupling J` symmetric with zero diagonal. "→ in probability" is: for every `t > 0`, the probability that the deviation exceeds `t` tends to `0`. "max > t" is "some entry exceeds t" (no max over an
empty index set at `n = 0`). -/
theorem lemma_2_9 (β : ℝ) (hβ : 0 < β) :
    ∀ t : ℝ, 0 < t →
      Tendsto (fun n : ℕ => disorderLaw β n {J | ∃ i k : Fin n, t < |coupling J i k|})
        atTop (nhds 0) := by sorry

end RankOneSK

-- Prove2me | Theorems.Thm_RankOneSK_lemma_2_8
-- name    : RankOneSK.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:28:58.33811+00:00
-- url     : https://prove2.me/theorems/546b87e4-bdf8-402f-8a87-7e48df424d00
-- title:
--   Lemma 2.8 — row norms of a β-GOE matrix: $\max_i|\sum_jJ_{ij}^2-\beta^2|\to0$ in probability
-- statement:
--   Let $\beta\ge0$ be fixed and let $J$ be an $n\times n$ β-GOE matrix.
--
--   **Lemma 2.8.** $\max_{i\in[n]}\big|\sum_jJ_{ij}^2-\beta^2\big|\to0$ in probability: for every $t>0$,
--   $$\Pr\Big[\max_{i\in[n]}\Big|\sum_jJ_{ij}^2-\beta^2\Big|>t\Big]\xrightarrow[n\to\infty]{}0 .$$
--
--   It controls the $\lambda^2$ and $d$ terms after summing the local inequality (25) over all pairs, in (26).
--
--   Differences from the source:
--   - encoding: convergence in probability → for every t > 0, the probability that the deviation exceeds t tends to 0; reason: the definition of convergence in probability
--   - encoding: max_i |…| > t → some row i with |…| > t; reason: equivalent
--   - encoding: J β-GOE: symmetric, J_ij iid N(0, β²/n) for i < j, J_ii = 0 → the published OAI.SKGap.disorderLaw β n on the entries above the diagonal, with coupling J the full symmetric zero-diagonal matrix; reason: the same law
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Lemma 2.8, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_SKHighTemperature

open OAI.SKGap MeasureTheory ProbabilityTheory Filter

namespace RankOneSK

/-- **Lemma 2.8.** Let `β ⩾ 0` be fixed and `J ∈ ℝ^{n×n}` the β-GOE matrix. Then
`max_{i∈[n]} |Σ_j J_ij² − β²| → 0` in probability.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Lemma 2.8, p.14.

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (±1 through `spinValue`), sites 0-based `Fin n`.
The β-GOE matrix `J` is the published `OAI.SKGap.Disorder n` under `disorderLaw β n`: entries
`J_ik`, `i < k`, i.i.d. `N(0, β²/n)`, `coupling J` symmetric with zero diagonal. "→ in probability" is: for every `t > 0`, the probability that the deviation exceeds `t` tends to `0`. "max > t" is "some row exceeds t". -/
theorem lemma_2_8 (β : ℝ) (hβ : 0 ≤ β) :
    ∀ t : ℝ, 0 < t →
      Tendsto (fun n : ℕ => disorderLaw β n
          {J | ∃ i : Fin n, t < |∑ k : Fin n, coupling J i k ^ 2 - β ^ 2|})
        atTop (nhds 0) := by sorry

end RankOneSK

-- Prove2me | Theorems.Thm_SortingCounterexamples_Optimal_lemma_4_4
-- name    : SortingCounterexamples.Optimal.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:30.053728+00:00
-- url     : https://prove2.me/theorems/233a0710-57ba-4908-81f2-86ed6b0edbdf
-- title:
--   Lemma 4.4 — $\mathbb E[\ell_t(X)]\le 1/\gamma$ on truthful and $\le 1+\gamma n$ on untruthful rounds, $X$ uniform on $C^\star$
-- statement:
--   Let $\gamma>0$, let $\sigma$ be the target ranking with cell $C^\star=C_\sigma$, and let $X$ be uniform on $C^\star$. Consider a round with query $\pi$ and returned pair $\{i,j\}$, $\pi$ placing $i$ before $j$, and surrogate loss $\ell_t(x)=(1+\gamma n(x_j-x_i))_+$.
--
--   1. If the round is truthful ($\sigma$ places $j$ before $i$), then $\mathbb E[\ell_t(X)]\le 1/\gamma$.
--   2. If the round is untruthful ($\sigma$ places $i$ before $j$), then $\mathbb E[\ell_t(X)]\le 1+\gamma n$.
--
--   Combined with Jensen's inequality, these bounds control the mass of the target cell (equations (3) and (6)).
--
--   **Formalization Note** The expectation is the lower Lebesgue integral of $\ell_t\ge0$ against the normalized restriction of Lebesgue measure to $C^\star$, so no integrability side condition is involved. The bounds are stated for every query ranking $\pi$, in particular for the algorithm's.
--
--   Differences from the source:
--   - generalization: one universal constant γ > 0, fixed sufficiently large → every γ > 0; reason: the statement holds for each γ > 0, so it specializes to the source's fixed γ
--   - generalization: a round of the weighted algorithm (query = sorted barycenter) → an arbitrary query ranking π and returned pair s; reason: the bounds depend only on the query's orientation of the pair; the algorithm's rounds are instances
--   - encoding: E[ℓ_t(X)] for X uniform on C⋆ → ∫⁻ ENNReal.ofReal ℓ against cond volume C⋆, compared with ENNReal.ofReal of the bound; reason: ℓ_t ≥ 0, so the lower Lebesgue integral equals the expectation
-- source:
--   Noga Alon, Shay Moran, Shlomo Moran, STOC 2027 submission #549 (October 2026), printed p. 17 / PDF p. 18, Lemma 4.4 (proof to printed p. 18 / PDF p. 19)

import Mathlib
import Definitions.Def_SortingCounterexamples_Optimal_WeightedUpdate

open MeasureTheory

namespace SortingCounterexamples.Optimal

/-- Lemma 4.4: for `X` uniform on the target cell `C_σ`, the surrogate loss of a round with
query `π` and returned pair `s` has expectation at most `1/γ` when `s` is truthful and at most
`1 + γ n` when it is untruthful. -/
theorem lemma_4_4 (γ : ℝ) (hγ : 0 < γ) {n : ℕ} (σ π : Ranking n) (s : ItemPair n) :
    (Truthful π σ s →
      ∫⁻ x, ENNReal.ofReal (loss γ π s x) ∂(cellUniform σ) ≤ ENNReal.ofReal (1 / γ)) ∧
    (¬ Truthful π σ s →
      ∫⁻ x, ENNReal.ofReal (loss γ π s x) ∂(cellUniform σ) ≤ ENNReal.ofReal (1 + γ * n)) := by sorry

end SortingCounterexamples.Optimal

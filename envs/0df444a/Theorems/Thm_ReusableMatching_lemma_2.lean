-- Prove2me | Theorems.Thm_ReusableMatching_lemma_2
-- name    : ReusableMatching.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:47.250115+00:00
-- url     : https://prove2.me/theorems/32d09303-e707-4253-ad4a-ffd6ff7548d1
-- title:
--   Lemma 2: the dual candidate (1)–(2) satisfies reverse weak duality
-- statement:
--   Let an OBMRR instance and $\beta>0$ be given, and let $\beta_j(Y)$, $\alpha_{i,t}(Y)$ be the random dual variables (1) and (2) of Periodic Reranking. With $\beta_j=\mathbb E_Y[\beta_j(Y)]$, $\alpha_{i,t}=\mathbb E_Y[\alpha_{i,t}(Y)]$ and $P$ the expected reward of Periodic Reranking,
--
--   $$
--   \sum_{i\in V}\sum_{t}\alpha_{i,t}+\sum_{j}\beta_j\ \le\ P,
--   $$
--
--   which is constraint (i) of Lemma 1. Pointwise, $\beta_j(Y)+\alpha_{i,j}(Y)=r_i$ on every pair $(i,j)$ of the matching $\mathrm{PR}(Y)$.
--
--   Differences from the source:
--   - encoding: E_Y[·] over i.i.d. U[0,1] seeds → Bochner integral with respect to seedMeasure, the product of the uniform measures on unitInterval; reason: Lean convention; the integrands are bounded
--   - reading: arg max over the available neighbours, no tie rule (Algorithm 1, p.8) → the least maximizer for a linear order on V (a fixed priority order; V and its order are arbitrary); reason: the paper fixes no tie rule; its proofs of Lemmas 4, 6 and 8 compare runs at fixed seeds and need a choice among tied resources that does not depend on the seeds
--   - encoding: arrivals 1, …, |U|; periods of length d with a dummy period before the first arrival (p.8) → arrivals Fin n numbered from 0; arrival t lies in period t / d + 1; period 0 is the dummy period; seeds indexed by V × Fin (n + 1); reason: Lean convention; same instances and same runs
--   - encoding: d ∈ ℕ (p.2) → 1 ≤ d, as a field of the instance; reason: the model ("unavailable for the next d − 1 periods") has no meaning at d = 0
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Lemma 2, p.8

import Mathlib
import Definitions.Def_ReusableMatching_dualBeta
import Definitions.Def_ReusableMatching_dualAlpha
import Definitions.Def_ReusableMatching_reward

namespace ReusableMatching

open MeasureTheory

/-- **Lemma 2 (reverse weak duality)** of Delong, Farhadi, Niazadeh, Sivan & Udwani,
arXiv:2110.07084v2, p.8: "The dual candidate given by (1) and (2) satisfies constraint (i) of
Lemma 1."

The dual candidate is `β_j = E_Y[β_j(Y)]`, `α_{i,t} = E_Y[α_{i,t}(Y)]` (p.8), with `β_j(Y)`,
`α_{i,t}(Y)` given by (1), (2); its objective is `D = ∑_{i,t} α_{i,t} + ∑_j β_j`, and the primal
value `P` is the expected reward of Periodic Reranking. Constraint (i) is `P ≥ D`.

**Formalization Note.** Expectations are Bochner integrals with respect to the uniform product law
of the seeds (`seedMeasure`). The parameter `β > 0` is the paper's standing range for the family
`g(x) = e^{β(x−1)}` (p.8). -/
theorem lemma_2 {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ : 0 < β) :
    (∑ i, ∑ t, ∫ Y, dualAlpha I β Y i t ∂(seedMeasure V n)) +
        ∑ j, ∫ Y, dualBeta I β Y j ∂(seedMeasure V n) ≤
      ∫ Y, reward I β Y ∂(seedMeasure V n) := by sorry

end ReusableMatching

-- Prove2me | Theorems.Thm_SmallLossGraph_proof_thm_3_6_item_1
-- name    : SmallLossGraph.proof_thm_3_6_item_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:17.560503+00:00
-- url     : https://prove2.me/theorems/5176c1b2-3b39-454f-8c5e-0c0564663d7c
-- title:
--   Proof of Theorem 3.6, item 1 — the algorithm's loss stays close to its expected loss
-- statement:
--   Let Algorithm 1 run a full-information algorithm $A$ with parameters $\varepsilon'>0$ and $\alpha$ against a deterministic adaptive adversary for $T$ rounds, drawing $I(t)\sim w^t$. For every $\delta'>0$, with probability at least $1-\delta'$,
--
--   $$
--   \sum_t\ell^t_{I(t)}-(1+\varepsilon')\sum_t\sum_i w^t_i\ell^t_i\le\frac{(1+\varepsilon')\ln(1/\delta')}{\varepsilon'} .
--   $$
--
--   This is the first of the three concentration steps in the proof of Theorem 3.6: $x_t=\ell^t_{I(t)}\in[0,1]$ has conditional mean $\sum_iw^t_i\ell^t_i$ given the past, and Lemma 3.7 applies.
--
--   **Formalization Note** The probability is the sum of the path probabilities $\prod_tw^t_{I(t)}$ over the arm paths where the inequality fails; the statement says it is at most $\delta'$.
--
--   Differences from the source:
--   - reading: for any δ′, ε > 0 (the display uses ε′) → for all δ′ > 0 and ε′ > 0; reason: the display's parameter is ε′; the printed ε is a typo
--   - generalization: inside Theorem 3.6: α bounds the independent sets of every G^t, A has the approximate-regret guarantee, ε′ = ε/5 → any α, any adaptive adversary, any full-information A, any ε′ > 0; reason: item 1 uses none of these hypotheses; the theorem's setting is a special case
--   - encoding: randomized play I(t) ∼ w^t against an adaptive adversary → deterministic adaptive adversary; probability as the sum of path probabilities ∏_t w^t_{I(t)}; rounds 0-based; reason: randomized adversaries are mixtures of deterministic ones; the path sum is the law of the run
--   - encoding: Algorithm 1, line 5, divides by 1 − Σ_{j∈F} p_j, undefined when every arm carrying probability is frozen → in that case w = p (sampling convention); reason: the case cannot occur for ε′ < 1 (Lemma 3.1), so no instance of the paper changes; the convention keeps w a probability vector
-- source:
--   Lykouris–Sridharan–Tardos, Small-loss bounds for online learning with partial information, arXiv:1711.03639v5, proof of Theorem 3.6, item 1, p.12

import Mathlib
import Definitions.Def_SmallLossGraph_Protocol
import Definitions.Def_SmallLossGraph_Freezing
import Definitions.Def_SmallLossGraph_Run

open scoped BigOperators

namespace SmallLossGraph

/-- **Proof of Theorem 3.6, item 1: the algorithm's loss is close to its expected loss.**
Lykouris–Sridharan–Tardos, arXiv:1711.03639v5, proof of Theorem 3.6, item 1, p.12: "we use
`x_t = ℓ^t_{I(t)}`, and note that its expectation conditioned on the previous losses is
`m_t = ∑_i w^t_i ℓ^t_i` so we obtain that, for any `δ′, ε > 0`, with probability at least
`(1 − δ′)`: `∑_t ℓ^t_{I(t)} − (1 + ε′) ∑_t ∑_i w^t_i ℓ^t_i ≤ (1 + ε′) ln(1/δ′)/ε′`."

Let Algorithm 1 run a full-information algorithm `A` with parameters `ε′ > 0` and `α` against an
adaptive adversary for `T` rounds, drawing `I(t) ∼ w^t`. For every `δ′ > 0`,
`Pr[ ∑_t ℓ^t_{I(t)} − (1 + ε′) ∑_t ∑_i w^t_i ℓ^t_i > (1 + ε′) ln(1/δ′)/ε′ ] ≤ δ′`.

**Formalization Note** Rounds are 0-based; the probability is the sum of the path probabilities
`∏_t w^t_{I(t)}` over the arm paths in the event. The statement holds for every `α` and every
adversary (no bound on independent sets is needed for item 1). For `ε′ ≥ 1` the sampling vector
uses the convention of `sampling` when every arm with probability is frozen. -/
theorem proof_thm_3_6_item_1 {d : ℕ} (T : ℕ) (A : FullInfoAlg d) (adv : Adversary d) (α : ℕ)
    (ε' δ' : ℝ) (hε' : 0 < ε') (hδ' : 0 < δ') :
    probEvent T A adv ε' α (fun s => (1 + ε') * Real.log (1 / δ') / ε' <
        ∑ t, runLoss adv s t (s t) - (1 + ε') * ∑ t, ∑ i, runW A adv ε' α s t i * runLoss adv s t i)
      ≤ δ' := by sorry

end SmallLossGraph

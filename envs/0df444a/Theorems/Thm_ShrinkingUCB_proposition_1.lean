-- Prove2me | Theorems.Thm_ShrinkingUCB_proposition_1
-- name    : ShrinkingUCB.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:51.716097+00:00
-- url     : https://prove2.me/theorems/957edd8b-d538-44bb-adc4-d997b78b57db
-- title:
--   Proposition 1 — conditions (1) and (2) hold for all $t,k$ with probability at least $1-\delta$
-- statement:
--   Let an instance, a reward table, a tie-break and an optimal set $S^*$ be given, with $d\ge1$, $1\le K\le N$, $T\ge1$, $\delta\in(0,1)$. If ConsUCB is run with $\alpha=\sqrt{d\ln((1+N+TN)/\delta)}+1$, then with probability at least $1-\delta$ the following conditions hold for all $t\in[T]$ and $k\in[K]$:
--
--   1. If $i_{t,k}\notin S^*$, then for all $i^*\in S^*\setminus S_t$,
--   $$
--   \mu(i^*)-\mu(i_{t,k})\le\mathrm{LCB}_{t+1}(i^*)-\mathrm{LCB}_t(i^*)+2\alpha\Delta_{t,k-1}(i_{t,k}).
--   $$
--   2. If $i_{t,k}\in S^*$, then
--   $$
--   0\le\mathrm{LCB}_{t+1}(i_{t,k})-\mathrm{LCB}_t(i_{t,k})+2\alpha\Delta_{t,k-1}(i_{t,k}).
--   $$
--
--   This is the key new statement of the paper's analysis: summing it over the selections makes the lower confidence bounds telescope over the periods.
--
--   Differences from the source:
--   - reading: S_t in the conditions, ∆_{t,k} "for all k ∈ [K]" → S_t is the final set of period t; ∆_{t,k} for k ∈ {0, …, K}; reason: the proof's step ③ needs i* never picked in period t, and the text uses k = 0 (p.16, p.17)
--   - reading: d, K, N, T unconstrained on the page and δ unstated → 1 ≤ d, 1 ≤ K ≤ N, 1 ≤ T, 0 < δ < 1; reason: "selects a set of K products from [N]" (p.9) needs K ≤ N; ln δ needs δ > 0; for δ ≥ 1 the claim is empty
--   - encoding: r_{t,i} for i ∈ S_t, independent across products and periods → an independent table of Bool outcomes r_{t,i}, t ∈ [T], i ∈ [N], of which the run reads the offered entries; reason: the standard representation of the model of p.9; it is what makes a non-anticipating S_t well defined
--   - reading: add a product j ∈ arg max → j is chosen by any deterministic function of the observed history, the selections so far in the period and the tied set, returning a member of the arg max; reason: p.9: the decision is "based on all the past information"; a rule reading unobserved outcomes is not an algorithm in that sense. A randomized rule with an independent seed is a mixture of these
--   - reading: S*, a fixed element of the arg max → every optimal K-set S*; reason: the arg max need not be a singleton, and R(T) does not depend on the choice
--   - encoding: with probability at least 1 − δ, the claim holds → P(the claim fails) ≤ δ, with P the outer measure on a possibly non-measurable event; reason: complement form; "≥ 1 − δ" in ℝ≥0∞ subtraction is avoided, and the two agree on measurable events
--   - encoding: A⁻¹ → Matrix.inv, total with value 0 on singular matrices; reason: every A_t and A_{t,k} dominates the identity, so the inverse is a true inverse
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, Proposition 1, p.17

import Definitions.Def_ShrinkingUCB_ConfidenceBounds
import Definitions.Def_ShrinkingUCB_IsOptimalSet
import Definitions.Def_ShrinkingUCB_alpha

open MeasureTheory

namespace ShrinkingUCB

/-- Proposition 1, p.17 of arXiv:1903.07844v2: if ConsUCB is run with
`α = √(d ln((1 + N + TN)/δ)) + 1`, then with probability at least `1 − δ`, for all `t ∈ [T]` and
`k ∈ [K]`, both conditions (1) and (2) hold. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d N : ℕ} (K T : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (hKN : K ≤ N) (hT : 1 ≤ T)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (I : LinearSemiBandit d N) (r : ℕ → Fin N → Ω → Bool) (hr : IsRewardTable I P T r)
    (tb : TieBreak N) (Sstar : Finset (Fin N)) (hS : IsOptimalSet I K Sstar) :
    P {ω | ¬ ∀ t ∈ Finset.Icc 1 T, ∀ k ∈ Finset.Icc 1 K,
      let α := alpha d N T δ
      let o := tableAt r ω
      (pick I tb α K o t k ∉ Sstar →
        ∀ istar ∈ Sstar \ offered I tb α K o t,
          I.μ istar - I.μ (pick I tb α K o t k) ≤
            LCB I tb α K o (t + 1) istar - LCB I tb α K o t istar
              + 2 * α * Delta I tb α K o t (k - 1) (pick I tb α K o t k)) ∧
      (pick I tb α K o t k ∈ Sstar →
        0 ≤ LCB I tb α K o (t + 1) (pick I tb α K o t k) - LCB I tb α K o t (pick I tb α K o t k)
          + 2 * α * Delta I tb α K o t (k - 1) (pick I tb α K o t k))}
      ≤ ENNReal.ofReal δ := by sorry

end ShrinkingUCB

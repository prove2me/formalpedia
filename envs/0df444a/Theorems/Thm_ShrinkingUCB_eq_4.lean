-- Prove2me | Theorems.Thm_ShrinkingUCB_eq_4
-- name    : ShrinkingUCB.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:20:01.216696+00:00
-- url     : https://prove2.me/theorems/95402d0b-4d01-4997-89b0-3adf7e04296a
-- title:
--   Eq. (4) — the confidence bounds hold for all $t\in[T+1]$ with probability at least $1-\delta$
-- statement:
--   Let an instance, a reward table on a probability space, and a tie-break be given, with $d\ge1$, $1\le K\le N$, $T\ge1$ and $\delta\in(0,1)$. Run ConsUCB with $\alpha=\sqrt{d\ln((1+N+TN)/\delta)}+1$. Then with probability at least $1-\delta$,
--
--   $$
--   \mathrm{LCB}_t(i)\le\mu(i)\le\mathrm{UCB}_t(i)\qquad\text{for all }i\in[N]\text{ and }t\in[T+1].
--   $$
--
--   This is the only probabilistic input of the regret analysis. It holds for ConsUCB because the selections inside a period read no outcome of that period.
--
--   Differences from the source:
--   - reading: Lemma 1 stated for SemiUCB at horizon T, with 1 + TN in α → the ConsUCB run, at all t ∈ [T + 1], with 1 + N + TN; reason: this is how the proof on p.17 uses Lemma 1: eq. (4) ranges over t ∈ [T + 1] and 1 + (T + 1)N = 1 + N + TN
--   - reading: d, K, N, T unconstrained on the page and δ unstated → 1 ≤ d, 1 ≤ K ≤ N, 1 ≤ T, 0 < δ < 1; reason: "selects a set of K products from [N]" (p.9) needs K ≤ N; ln δ needs δ > 0; for δ ≥ 1 the claim is empty
--   - encoding: r_{t,i} for i ∈ S_t, independent across products and periods → an independent table of Bool outcomes r_{t,i}, t ∈ [T], i ∈ [N], of which the run reads the offered entries; reason: the standard representation of the model of p.9; it is what makes a non-anticipating S_t well defined
--   - reading: add a product j ∈ arg max → j is chosen by any deterministic function of the observed history, the selections so far in the period and the tied set, returning a member of the arg max; reason: p.9: the decision is "based on all the past information"; a rule reading unobserved outcomes is not an algorithm in that sense. A randomized rule with an independent seed is a mixture of these
--   - encoding: with probability at least 1 − δ, the claim holds → P(the claim fails) ≤ δ, with P the outer measure on a possibly non-measurable event; reason: complement form; "≥ 1 − δ" in ℝ≥0∞ subtraction is avoided, and the two agree on measurable events
--   - encoding: A⁻¹ → Matrix.inv, total with value 0 on singular matrices; reason: every A_t and A_{t,k} dominates the identity, so the inverse is a true inverse
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, Eq. (4), p.17 (Lemma 1, p.11, applied to ConsUCB)

import Definitions.Def_ShrinkingUCB_ConfidenceBounds
import Definitions.Def_ShrinkingUCB_alpha

open MeasureTheory

namespace ShrinkingUCB

/-- Eq. (4), p.17 of arXiv:1903.07844v2 (Lemma 1 applied to ConsUCB): with probability at least
`1 − δ`, `LCB_t(i) ≤ µ(i) ≤ UCB_t(i)` for all `i ∈ [N]` and `t ∈ [T + 1]`.

**Formalization Note.** Periods and selections are `1`-based, `Real.log` is natural, and the
failure probability is the outer measure of the bad event. -/
theorem eq_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d N : ℕ} (K T : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (hKN : K ≤ N) (hT : 1 ≤ T)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (I : LinearSemiBandit d N) (r : ℕ → Fin N → Ω → Bool) (hr : IsRewardTable I P T r)
    (tb : TieBreak N) :
    P {ω | ¬ ConfidenceHolds I tb (alpha d N T δ) K (tableAt r ω) T} ≤ ENNReal.ofReal δ := by sorry

end ShrinkingUCB

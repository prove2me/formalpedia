-- Prove2me | Theorems.Thm_ShrinkingUCB_theorem_3
-- name    : ShrinkingUCB.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:20:13.223819+00:00
-- url     : https://prove2.me/theorems/5edbd61b-9053-4ff2-b66c-c97a30db7ad1
-- title:
--   Theorem 3 — ConsUCB has regret at most $K+\alpha K+10\alpha\sqrt{dKT\log(KT)}$ with probability at least $1-\delta$
-- statement:
--   Consider $N$ products with features $x_i\in\mathbb R^d$ and an unknown $\theta^*$, with $\|\theta^*\|\le1$, $\|x_i\|\le1$, $\mu(i)=x_i^\top\theta^*\in[0,1]$. Let $(r_{t,i})$ be independent binary outcomes with mean $\mu(i)$, let $S^*$ be an optimal set of $K$ products, and let $d\ge1$, $1\le K\le N$, $T\ge1$, $\delta\in(0,1)$. If ConsUCB is run with
--
--   $$
--   \alpha=\sqrt{d\ln\Big(\frac{1+N+TN}{\delta}\Big)}+1,
--   $$
--
--   with any tie-break that is a function of the observed history, then with probability at least $1-\delta$,
--
--   $$
--   R(T)\le K+\alpha K+10\alpha\sqrt{dKT\log(KT)}.
--   $$
--
--   This is the paper's main result. The term linear in $K$, the fixed cost, is $\tilde O(K\sqrt d)$, smaller than that of the standard UCB analysis by a factor of $d$, and the variable cost is $\tilde O(d\sqrt{KT})$.
--
--   **Formalization Note** The statement includes $K=T=1$, where the bound follows from $R(T)\le KT\le K+\alpha K$.
--
--   Differences from the source:
--   - generalization: the regret is Õ(K√d + d√(KT)) → R(T) ≤ K + αK + 10α√(dKT log(KT)), the explicit form printed on p.19; reason: it is the bound the proof establishes, and it specializes to the Õ form by the milestone bound_simplified
--   - reading: d, K, N, T unconstrained on the page and δ unstated → 1 ≤ d, 1 ≤ K ≤ N, 1 ≤ T, 0 < δ < 1; reason: "selects a set of K products from [N]" (p.9) needs K ≤ N; ln δ needs δ > 0; for δ ≥ 1 the claim is empty
--   - encoding: r_{t,i} for i ∈ S_t, independent across products and periods → an independent table of Bool outcomes r_{t,i}, t ∈ [T], i ∈ [N], of which the run reads the offered entries; reason: the standard representation of the model of p.9; it is what makes a non-anticipating S_t well defined
--   - reading: add a product j ∈ arg max → j is chosen by any deterministic function of the observed history, the selections so far in the period and the tied set, returning a member of the arg max; reason: p.9: the decision is "based on all the past information"; a rule reading unobserved outcomes is not an algorithm in that sense. A randomized rule with an independent seed is a mixture of these
--   - reading: S*, a fixed element of the arg max → every optimal K-set S*; reason: the arg max need not be a singleton, and R(T) does not depend on the choice
--   - encoding: with probability at least 1 − δ, the claim holds → P(the claim fails) ≤ δ, with P the outer measure on a possibly non-measurable event; reason: complement form; "≥ 1 − δ" in ℝ≥0∞ subtraction is avoided, and the two agree on measurable events
--   - encoding: A⁻¹ → Matrix.inv, total with value 0 on singular matrices; reason: every A_t and A_{t,k} dominates the identity, so the inverse is a true inverse
--   - reading: log(KT) → Real.log, the natural logarithm; reason: §4 writes ln throughout, and the log of Lemma 2 comes from Chu et al. (2011), whose logarithm is natural; the base changes the bound, so this is a reading, not an encoding
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, Theorem 3, p.18; explicit form at the end of its proof, p.19

import Definitions.Def_ShrinkingUCB_IsOptimalSet
import Definitions.Def_ShrinkingUCB_alpha
import Definitions.Def_ShrinkingUCB_regret

open MeasureTheory

namespace ShrinkingUCB

/-- Theorem 3, p.18 of arXiv:1903.07844v2, in the explicit form printed at the end of its proof,
p.19: if ConsUCB is run with `α = √(d ln((1 + N + TN)/δ)) + 1`, then with probability at least
`1 − δ`, `R(T) ≤ K + αK + 10α√(dKT log(KT))`.

**Formalization Note.** Periods and selections are `1`-based and `log` is natural. The bound holds
for every tie-break of the arg max (a deterministic function of the observed history) and every
optimal set `S*`, and at `K = T = 1`. The failure probability is the outer measure of the bad
event. -/
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d N : ℕ} (K T : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (hKN : K ≤ N) (hT : 1 ≤ T)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (I : LinearSemiBandit d N) (r : ℕ → Fin N → Ω → Bool) (hr : IsRewardTable I P T r)
    (tb : TieBreak N) (Sstar : Finset (Fin N)) (hS : IsOptimalSet I K Sstar) :
    P {ω | (K : ℝ) + alpha d N T δ * K
        + 10 * alpha d N T δ * √((d : ℝ) * K * T * Real.log ((K : ℝ) * T))
          < regret I tb (alpha d N T δ) K Sstar T (tableAt r ω)} ≤ ENNReal.ofReal δ := by sorry

end ShrinkingUCB

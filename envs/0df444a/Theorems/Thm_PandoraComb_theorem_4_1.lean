-- Prove2me | Theorems.Thm_PandoraComb_theorem_4_1
-- name    : PandoraComb.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:45.742999+00:00
-- url     : https://prove2.me/theorems/0a41bec9-49a7-43e5-9cbc-737d447f1009
-- title:
--   Theorem 4.1 — with a submodular cost some fixed order strategy with thresholds is optimal (corrected: thresholds in $\mathbb R\cup\{+\infty\}$)
-- statement:
--   Let $\mathcal I=(D_1,\dots,D_n,c)$ be an instance of Pandora's problem with combinatorial cost: the box values $V_i\sim D_i$ are independent, non-negative and have finite expectations, and the cost $c$ of inspecting a set of boxes satisfies $c(\emptyset)=0$, is monotone, and is **submodular**:
--   $$c(x\mid B)\le c(x\mid A)\qquad\text{for all }A\subseteq B,\ x\notin B,\quad c(x\mid S)=c(S\cup\{x\})-c(S).$$
--
--   Then there are an ordering $\sigma$ of the boxes and thresholds $t_0,\dots,t_{n-1}\in\mathbb R\cup\{\pm\infty\}$ such that the fixed order strategy with thresholds $(\sigma,t)$ (open $\sigma(0),\sigma(1),\dots$ in turn, halting at round $k$ as soon as the best value seen so far is at least $t_k$) is admissible and
--
--   $$u(\mathcal I;\pi)\ \le\ u\big(\mathcal I;(\sigma,t)\big)$$
--
--   for every admissible strategy $\pi$, including strategies that choose the next box adaptively and randomize.
--
--   Weitzman's theorem gives this structure for additive costs; the theorem shows that it survives for every submodular cost, so that an optimal strategy never needs to adapt the order of inspection, only the time of stopping.
--
--   Differences from the source:
--   - correction: fixed order strategy with thresholds t_1, …, t_n ∈ ℝ (p.7) → thresholds t : Fin n → EReal (a threshold +∞ never halts); reason: with real thresholds the statement is false: two i.i.d. Exp(1) boxes, c ≡ 0; opening both is optimal (utility 3/2), but any real t_2 halts after one box with positive probability and loses utility; the proof of Observation 1 (p.33) itself sets t_i = ∞ when C_i = ∅
--   - encoding: rounds i = 1, …, n, permutation σ : [n] → [n], "maximum value inspected so far" (p.7) → rounds k = 0, …, n−1, σ : Fin n ≃ ι, halt at round k iff t k ≤ max(0, maximum observed so far); reason: index shift only; the maximum so far is 0 before the first box, as in the proof of Observation 1 (x ≥ 0, p.33)
--   - reading: "there exists an optimal strategy that is …" → the strategy of the stated form is admissible and its utility is at least that of every admissible strategy; reason: this says that an optimal strategy exists and that one is of the stated form, without presupposing an optimum
--   - encoding: Π, all (randomized) strategies, deciding from the sequence of opened boxes and realized values so far, with coins tossed a priori (p.7) → admissible strategies: decisions read the ordered history and one uniform seed s ∈ [0,1] independent of the values, and are measurable in the observed values and the seed; reason: one uniform seed generates any finite family of coin tosses; measurability is what makes E[V(π)] and E[c(S(π))] defined, and it holds for every strategy the paper uses
--   - encoding: V(π) = max over S(π) of V_i, u(π) = E[V(π)] − E[c(S(π))] (p.7) → reward max(0, max observed value), utility = expectation of reward minus c(set of opened boxes); reason: values are non-negative a.s. and the empty strategy has utility 0 (pp.8, 24), so the two rewards agree a.s.
--   - encoding: boxes [n], c : 2^[n] → ℝ≥0 normalized and monotone (p.7) → boxes a finite type ι, c : Finset ι → ℝ with c ∅ = 0 and Monotone c; reason: relabeling [n] as ι changes no instance; c ≥ 0 follows from c ∅ = 0 and monotonicity
--   - encoding: a strategy chooses an uninspected box or halts (p.7) → a request for an already opened box halts the run; at most |ι| rounds; reason: a legal strategy never makes such a request, and |ι| rounds suffice to open every box
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, Theorem 4.1, p.20 (announced as Theorem 2, p.4; proof pp.20–21)

import Definitions.Def_PandoraComb_Model
import Definitions.Def_PandoraComb_FixedOrder
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular

open MeasureTheory

namespace PandoraComb

/-- **Theorem 4.1** (Berger, Ezra, Feldman & Fusco, *Pandora’s Problem with Combinatorial Cost*,
arXiv:2303.01078v1, p.20; announced as Theorem 2, p.4): "For every instance I = (D1, . . . , Dn, c)
where c is submodular, there exists an optimal strategy that is a fixed order strategy with
thresholds."

**Formalization Note.** The instance is `IsInstance D c` (§2, p.7: independent non-negative laws
with finite expectations, cost normalized and monotone). The conclusion is stated as: some fixed
order threshold strategy is admissible and its utility is at least that of **every** admissible
strategy (adaptive in the order and in stopping, randomized through the seed). This says that an
optimal strategy exists and that one optimal strategy is a fixed order strategy with thresholds.
Thresholds take values in `EReal` (a threshold `+∞` never halts); with real thresholds the
statement is false (two i.i.d. Exp(1) boxes and cost `0`). -/
theorem theorem_4_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → Measure ℝ)
    (c : Finset ι → ℝ) (hI : IsInstance D c) (hsub : SubsamplingSM.Offline.IsSubmodular c) :
    ∃ (σ : Fin (Fintype.card ι) ≃ ι) (t : Fin (Fintype.card ι) → EReal),
      Admissible (thresholdStrategy σ t) ∧
        ∀ π : Strategy ι, Admissible π → utility D c π ≤ utility D c (thresholdStrategy σ t) := by sorry

end PandoraComb

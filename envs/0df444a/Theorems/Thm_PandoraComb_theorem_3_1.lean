-- Prove2me | Theorems.Thm_PandoraComb_theorem_3_1
-- name    : PandoraComb.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:26.142992+00:00
-- url     : https://prove2.me/theorems/dbcf5d8a-795f-4af1-b42f-942afd4fc63f
-- title:
--   Theorem 3.1 — on every Bernoulli instance with submodular cost some impulsive strategy is optimal
-- statement:
--   Let $\mathcal I$ be a Bernoulli instance: box $i$ has value $v_i\ge0$ with probability $p_i\in[0,1]$ and $0$ otherwise, independently, and the cost $c$ is normalized, monotone and submodular. Then there is an impulsive strategy $\pi=(i_1,\dots,i_k)$ (distinct boxes; inspect them in order, halting at the first non-zero value) that is admissible and satisfies
--
--   $$u(\mathcal I;\pi')\ \le\ u(\mathcal I;\pi)$$
--
--   for every admissible strategy $\pi'$, adaptive and randomized strategies included.
--
--   This is the paper's structural result for Bernoulli instances; §4 transfers it to arbitrary distributions.
--
--   Differences from the source:
--   - reading: "there exists an optimal strategy that is …" → the strategy of the stated form is admissible and its utility is at least that of every admissible strategy; reason: this says that an optimal strategy exists and that one is of the stated form, without presupposing an optimum
--   - encoding: Bernoulli instance: box i has value v_i with probability p_i, 0 otherwise (p.7), non-negative distributions (p.7) → laws bernoulliLaw (v i) (p i) = (1 − p_i)δ_0 + p_i δ_{v_i} with v_i ≥ 0, p_i ∈ [0, 1]; reason: these are exactly the weighted Bernoulli laws; finite expectation is automatic
--   - encoding: impulsive strategy: a tuple of boxes without repetition, halting at the first non-zero value (pp.7–9) → impulsive l for a list l with l.Nodup; reason: halting early at a zero value is the impulsive strategy of a shorter tuple
--   - encoding: Π, all (randomized) strategies, deciding from the sequence of opened boxes and realized values so far, with coins tossed a priori (p.7) → admissible strategies: decisions read the ordered history and one uniform seed s ∈ [0,1] independent of the values, and are measurable in the observed values and the seed; reason: one uniform seed generates any finite family of coin tosses; measurability is what makes E[V(π)] and E[c(S(π))] defined, and it holds for every strategy the paper uses
--   - encoding: V(π) = max over S(π) of V_i, u(π) = E[V(π)] − E[c(S(π))] (p.7) → reward max(0, max observed value), utility = expectation of reward minus c(set of opened boxes); reason: values are non-negative a.s. and the empty strategy has utility 0 (pp.8, 24), so the two rewards agree a.s.
--   - encoding: boxes [n], c : 2^[n] → ℝ≥0 normalized and monotone (p.7) → boxes a finite type ι, c : Finset ι → ℝ with c ∅ = 0 and Monotone c; reason: relabeling [n] as ι changes no instance; c ≥ 0 follows from c ∅ = 0 and monotonicity
--   - encoding: a strategy chooses an uninspected box or halts (p.7) → a request for an already opened box halts the run; at most |ι| rounds; reason: a legal strategy never makes such a request, and |ι| rounds suffice to open every box
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, Theorem 3.1, p.8 (proof p.8–9)

import Definitions.Def_PandoraComb_Model
import Definitions.Def_PandoraComb_Bernoulli
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular

open MeasureTheory

namespace PandoraComb

/-- **Theorem 3.1** (arXiv:2303.01078v1, p.8): "For every Bernoulli instance with a submodular
cost function there exists an optimal strategy that is impulsive."

**Formalization Note.** Bernoulli instance: values `v i ≥ 0`, probabilities `p i ∈ [0, 1]`; the
cost is normalized and monotone (§2, p.7) and submodular. The conclusion: some impulsive strategy
(a tuple without repetition) is admissible and its utility is at least that of every admissible
strategy, adaptive and randomized ones included. -/
theorem theorem_3_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (v p : ι → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (c : Finset ι → ℝ) (hc0 : c ∅ = 0) (hmono : Monotone c)
    (hsub : SubsamplingSM.Offline.IsSubmodular c) :
    ∃ l : List ι, l.Nodup ∧ Admissible (impulsive l) ∧
      ∀ π : Strategy ι, Admissible π →
        utility (bernoulliInstance v p) c π ≤ utility (bernoulliInstance v p) c (impulsive l) := by sorry

end PandoraComb

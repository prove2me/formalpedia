-- Prove2me | Theorems.Thm_PandoraComb_lemma_3_1
-- name    : PandoraComb.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:35.065003+00:00
-- url     : https://prove2.me/theorems/d626e1e4-e9c6-4250-bbdb-ec63699635c3
-- title:
--   Lemma 3.1 — if a two-branch strategy with impulsive branches is optimal, some impulsive strategy is optimal
-- statement:
--   Let $\mathcal I$ be a Bernoulli instance (box $i$ has value $v_i\ge0$ with probability $p_i\in[0,1]$ and $0$ otherwise) whose cost $c$ is normalized, monotone and submodular. Suppose some strategy of the following form is optimal, i.e. its utility is at least that of every admissible strategy:
--
--   1. inspect a first box $r$ with $v_r>0$ and $p_r>0$;
--   2. if $V_r=v_r$, execute an impulsive sub-strategy $\pi^Y$;
--   3. if $V_r=0$, execute an impulsive sub-strategy $\pi^N$,
--
--   where $\pi^Y,\pi^N$ are tuples of distinct boxes not containing $r$. Then there is an impulsive strategy $\pi$ (a tuple of distinct boxes) that is admissible and satisfies $u(\mathcal I;\pi')\le u(\mathcal I;\pi)$ for every admissible strategy $\pi'$.
--
--   This is the main technical result of the paper: it is the inductive step of Theorem 3.1.
--
--   Differences from the source:
--   - reading: π^Y, π^N impulsive sub-strategies executed after box r (p.8) → branch r πY πN: after r, the sub-strategy halts at the first non-zero value among the boxes opened after r (§3.1, p.9: "(1,2,7) … halts if V1 = v1"); reason: the §3.1 convention used in the proof of Lemma 3.1; under the other reading (impulsive for the residual instance I_Y of p.9) the lemma is also implied by Theorem 3.1
--   - reading: "there exists an optimal strategy that is …" → the strategy of the stated form is admissible and its utility is at least that of every admissible strategy; reason: this says that an optimal strategy exists and that one is of the stated form, without presupposing an optimum
--   - encoding: Bernoulli instance: box i has value v_i with probability p_i, 0 otherwise (p.7), non-negative distributions (p.7) → laws bernoulliLaw (v i) (p i) = (1 − p_i)δ_0 + p_i δ_{v_i} with v_i ≥ 0, p_i ∈ [0, 1]; reason: these are exactly the weighted Bernoulli laws; finite expectation is automatic
--   - encoding: impulsive strategy: a tuple of boxes without repetition, halting at the first non-zero value (pp.7–9) → impulsive l for a list l with l.Nodup; reason: halting early at a zero value is the impulsive strategy of a shorter tuple
--   - encoding: Π, all (randomized) strategies, deciding from the sequence of opened boxes and realized values so far, with coins tossed a priori (p.7) → admissible strategies: decisions read the ordered history and one uniform seed s ∈ [0,1] independent of the values, and are measurable in the observed values and the seed; reason: one uniform seed generates any finite family of coin tosses; measurability is what makes E[V(π)] and E[c(S(π))] defined, and it holds for every strategy the paper uses
--   - encoding: V(π) = max over S(π) of V_i, u(π) = E[V(π)] − E[c(S(π))] (p.7) → reward max(0, max observed value), utility = expectation of reward minus c(set of opened boxes); reason: values are non-negative a.s. and the empty strategy has utility 0 (pp.8, 24), so the two rewards agree a.s.
--   - encoding: boxes [n], c : 2^[n] → ℝ≥0 normalized and monotone (p.7) → boxes a finite type ι, c : Finset ι → ℝ with c ∅ = 0 and Monotone c; reason: relabeling [n] as ι changes no instance; c ≥ 0 follows from c ∅ = 0 and monotonicity
--   - encoding: a strategy chooses an uninspected box or halts (p.7) → a request for an already opened box halts the run; at most |ι| rounds; reason: a legal strategy never makes such a request, and |ι| rounds suffice to open every box
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, Lemma 3.1, p.8 (proof §3.1–3.2, pp.9–17)

import Definitions.Def_PandoraComb_Model
import Definitions.Def_PandoraComb_Bernoulli
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular

open MeasureTheory

namespace PandoraComb

/-- **Lemma 3.1** (arXiv:2303.01078v1, p.8): "Let I be a Bernoulli instance with a submodular
cost function. If there exists an optimal strategy for I of the following form:
• Inspect some first box, denoted r, that follows the distribution Vr = vr > 0 with probability
pr > 0.
• If Vr = vr, execute an impulsive sub-strategy π^Y.
• If Vr = 0, execute an impulsive sub-strategy π^N.
Then, there exists an optimal strategy for I which is impulsive."

**Formalization Note.** Bernoulli instance: values `v i ≥ 0`, probabilities `p i ∈ [0, 1]`; the
cost is normalized and monotone (§2, p.7) and submodular. The two-branch strategy is
`branch r πY πN` (sub-strategies are tuples without repetition and do not contain `r`); "optimal"
means: utility at least that of every admissible strategy. -/
theorem lemma_3_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (v p : ι → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (c : Finset ι → ℝ) (hc0 : c ∅ = 0) (hmono : Monotone c)
    (hsub : SubsamplingSM.Offline.IsSubmodular c) (r : ι) (hvr : 0 < v r) (hpr : 0 < p r)
    (πY πN : List ι) (hY : πY.Nodup) (hN : πN.Nodup) (hrY : r ∉ πY) (hrN : r ∉ πN)
    (hopt : ∀ π : Strategy ι, Admissible π →
      utility (bernoulliInstance v p) c π ≤ utility (bernoulliInstance v p) c (branch r πY πN)) :
    ∃ l : List ι, l.Nodup ∧ Admissible (impulsive l) ∧
      ∀ π : Strategy ι, Admissible π →
        utility (bernoulliInstance v p) c π ≤ utility (bernoulliInstance v p) c (impulsive l) := by sorry

end PandoraComb

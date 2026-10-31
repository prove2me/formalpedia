-- Prove2me | Theorems.Thm_PandoraComb_lemma_3_2
-- name    : PandoraComb.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:06.879094+00:00
-- url     : https://prove2.me/theorems/30dae635-e040-453e-a379-f75fe63aa8a9
-- title:
--   Lemma 3.2 — $p(\pi^Y)<p(\pi^N)$ for the optimal two-branch strategy of §3.1
-- statement:
--   Let $\mathcal I$ be a Bernoulli instance (weights $v_i\ge0$, probabilities $p_i\in[0,1]$) with a cost $c$ that is normalized, monotone and submodular. Let $r$ be a box with $v_r>0$ and $p_r>0$, and let $\pi^Y,\pi^N$ be impulsive strategies (tuples of distinct boxes, not containing $r$). Assume:
--
--   1. the two-branch strategy "inspect $r$; if $V_r\neq0$ run $\pi^Y$, else run $\pi^N$" is optimal: its utility is at least that of every admissible strategy;
--   2. $v_i\ge v_r$ for every box $i$ of $\pi^Y$;
--   3. no impulsive strategy achieves the utility of this two-branch strategy.
--
--   Then
--   $$p(\pi^Y)<p(\pi^N),\qquad p(\pi)=1-\prod_{i\in\pi}(1-p_i).$$
--
--   This is the first step of the proof by contradiction of Lemma 3.1. Assumption 3 is that proof's contradiction hypothesis, so by Theorem 3.1 assumptions 1 and 3 never hold together. The content is the contrapositive: if the two-branch strategy is optimal, $v_i\ge v_r$ on $\pi^Y$ and $p(\pi^Y)\ge p(\pi^N)$, then some impulsive strategy achieves its utility.
--
--   Differences from the source:
--   - generalization: the full setup of §3.1 (pp.9–10): v_i > 0 and p_i > 0 for every box, at most one deterministic box in π^Y and in π^N and it is last, π^Y nonempty, π* maximizing |π^Y| + |π^N| → only the hypotheses the proof uses: branch optimal, v_i ≥ v_r on π^Y, no optimal impulsive strategy, v_r > 0, p_r > 0; reason: the omitted assumptions are never used by the proof (p.12); the §3.1 setup is an instance
--   - reading: π^Y, π^N impulsive sub-strategies executed after box r (p.8) → branch r πY πN: after r, the sub-strategy halts at the first non-zero value among the boxes opened after r (§3.1, p.9: "(1,2,7) … halts if V1 = v1"); reason: the §3.1 convention used in the proof of Lemma 3.1; under the other reading (impulsive for the residual instance I_Y of p.9) the lemma is also implied by Theorem 3.1
--   - encoding: Bernoulli instance: box i has value v_i with probability p_i, 0 otherwise (p.7), non-negative distributions (p.7) → laws bernoulliLaw (v i) (p i) = (1 − p_i)δ_0 + p_i δ_{v_i} with v_i ≥ 0, p_i ∈ [0, 1]; reason: these are exactly the weighted Bernoulli laws; finite expectation is automatic
--   - encoding: impulsive strategy: a tuple of boxes without repetition, halting at the first non-zero value (pp.7–9) → impulsive l for a list l with l.Nodup; reason: halting early at a zero value is the impulsive strategy of a shorter tuple
--   - encoding: Π, all (randomized) strategies, deciding from the sequence of opened boxes and realized values so far, with coins tossed a priori (p.7) → admissible strategies: decisions read the ordered history and one uniform seed s ∈ [0,1] independent of the values, and are measurable in the observed values and the seed; reason: one uniform seed generates any finite family of coin tosses; measurability is what makes E[V(π)] and E[c(S(π))] defined, and it holds for every strategy the paper uses
--   - encoding: V(π) = max over S(π) of V_i, u(π) = E[V(π)] − E[c(S(π))] (p.7) → reward max(0, max observed value), utility = expectation of reward minus c(set of opened boxes); reason: values are non-negative a.s. and the empty strategy has utility 0 (pp.8, 24), so the two rewards agree a.s.
--   - encoding: boxes [n], c : 2^[n] → ℝ≥0 normalized and monotone (p.7) → boxes a finite type ι, c : Finset ι → ℝ with c ∅ = 0 and Monotone c; reason: relabeling [n] as ι changes no instance; c ≥ 0 follows from c ∅ = 0 and monotonicity
--   - encoding: a strategy chooses an uninspected box or halts (p.7) → a request for an already opened box halts the run; at most |ι| rounds; reason: a legal strategy never makes such a request, and |ι| rounds suffice to open every box
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, Lemma 3.2, p.12 (setup of §3.1, pp.9–10)

import Definitions.Def_PandoraComb_Model
import Definitions.Def_PandoraComb_Bernoulli
import Definitions.Def_PandoraComb_ClosedForms
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular

open MeasureTheory

namespace PandoraComb

/-- **Lemma 3.2** (arXiv:2303.01078v1, p.12): "It holds that p(π^Y) < p(π^N)."

**Formalization Note.** The lemma is stated inside the proof of Lemma 3.1 under the setup of §3.1
(pp.9–10). It is formalized with the hypotheses of that setup that its proof uses: a Bernoulli
instance (values `v i ≥ 0`, probabilities `p i ∈ [0, 1]`) with a normalized, monotone,
submodular cost; a first box `r` with `v r > 0`, `p r > 0`; impulsive sub-strategies `πY`, `πN`
(tuples without repetition, not containing `r`) such that the strategy `branch r πY πN` is
optimal among all admissible strategies; `v i ≥ v r` for every `i ∈ π^Y` (p.9); and the
proof-by-contradiction assumption of p.10 that no impulsive strategy achieves the utility of this
optimal strategy. `p(π) = 1 − ∏_{i ∈ π} (1 − p_i)` (p.10). -/
theorem lemma_3_2 {ι : Type*} [Fintype ι] [DecidableEq ι] (v p : ι → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (c : Finset ι → ℝ) (hc0 : c ∅ = 0) (hmono : Monotone c)
    (hsub : SubsamplingSM.Offline.IsSubmodular c) (r : ι) (hvr : 0 < v r) (hpr : 0 < p r)
    (πY πN : List ι) (hY : πY.Nodup) (hN : πN.Nodup) (hrY : r ∉ πY) (hrN : r ∉ πN)
    (hopt : ∀ π : Strategy ι, Admissible π →
      utility (bernoulliInstance v p) c π ≤ utility (bernoulliInstance v p) c (branch r πY πN))
    (hYv : ∀ i ∈ πY, v r ≤ v i)
    (hnot : ∀ l : List ι, l.Nodup →
      utility (bernoulliInstance v p) c (impulsive l) <
        utility (bernoulliInstance v p) c (branch r πY πN)) :
    pL p πY < pL p πN := by sorry

end PandoraComb

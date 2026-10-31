-- Prove2me | Theorems.Thm_ParallelSmallWorlds_SEU_lemma_1_b
-- name    : ParallelSmallWorlds.SEU.lemma_1_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:15.241132+00:00
-- url     : https://prove2.me/theorems/01ac672d-47fe-4d6c-b077-32d355e9dbe5
-- title:
--   Lemma 1(b): countable additivity under PSW7 (corrected: strict PSW5(b); uniqueness among calibrated probabilities)
-- statement:
--   Let a small world have a σ-field of events $Q$ and satisfy Axioms PSW1–PSW7 (with the two empty events identified) and the strict form C1 of Axiom PSW5(b). Then the calibrated probability $P=P_\Theta$ satisfies:
--
--   1. $P(\Theta)=1$, $P(R)\ge0$ for every event, and for every sequence of pairwise disjoint events $R_1,R_2,\dots$
--   $$\sum_{i=1}^\infty P(R_i)=P\Bigl(\bigcup_{i=1}^\infty R_i\Bigr),$$
--   so $P$ is a countably additive probability on $Q$;
--   2. for all events $R,S$, $R\succeq_\Theta S\iff P(R)\ge P(S)$;
--   3. $P$ is the only function with $P'(R)\in[0,1]$ and $R\sim_\Theta[0,P'(R)]$ for every event $R$.
--
--   The continuity axiom PSW7 is what upgrades the finitely additive probability of Lemma 1(a) to a measure.
--
--   Differences from the source:
--   - correction: PSW5(b) with weak conclusions only (p.21) → also the strict form (structure CorrectionC1): R ⪰ E, S ⪰ F with one strict gives R ∪ S ≻ E ∪ F, and dually; reason: the proof's step (12) uses 'the implication of PSW5 for strictly more likely'; without it the statement is false: Θ = {a,b}, events ranked by v(∅)=0, v{a}=v{b}=0.6, v(Θ)=1, reference events by Lebesgue measure, satisfies PSW1–PSW8 as printed, yet π{a}+π{b} = 1.2 ≠ 1 = πΘ
--   - correction: 'unique … probability distribution PΘw … agreeing with ⪰Θw' (uniqueness among all agreeing probabilities) → uniqueness among functions P with P(R) ∈ [0,1] and R ∼Θw [0,P(R)] for every event R; reason: uniqueness among agreeing probabilities is false: Θ = {a,b}, v{a}=0.7, v{b}=0.3 and Lebesgue measure on B satisfy every axiom (with C1), and both (0.7, 0.3) and (0.6, 0.4) agree with ⪰Θw on Qw; the proof's 'πR is unique' is uniqueness of the calibration
--   - encoding: ∀ w = 1,2,…,W (each small world separately) → one arbitrary small world W : SmallWorld Θ C; reason: every hypothesis and every conclusion concerns a single world; the statement for an arbitrary world is the statement for each w
--   - encoding: ⪰Θw on the set union Qw ∪ B, in which ∅ is a single element → lik on the disjoint sum Set Θ ⊕ Set ℝ, with ∅_Θ ∼Θw ∅_B imposed (field empty_identified of LikelihoodAxioms); reason: the disjoint sum has two copies of ∅; identifying them restores the paper's single empty set (reading R6), which step (10) uses
--   - generalization: set union Qw ∪ B (an event of Θw equal as a set to a reference event is the same element) → disjoint sum: events of Θ are never identified with reference events; reason: only a weaker hypothesis: a relation on the set union pulls back to one on the disjoint sum satisfying every axiom, so the Lean statement specializes to the paper's
--   - reading: B, 'the σ-field of open and closed intervals on [0,1]'; PSW2 for 'intervals, open or closed' → RefEvents = measurable (Borel) subsets of [0,1]; PSW2 for [a,b] and (a,b), 0 ≤ a ≤ b ≤ 1, including the degenerate {a} and ∅; reason: a σ-field is read as the one these intervals generate (reading R5); half-open intervals are not added to PSW2, which would strengthen it
--   - reading: PΘw, the probability of Lemma 1 → calib W R = inf{π ∈ [0,1] | [0,π] ⪰Θw R}; reason: the proof defines PΘw(R) = πR, the unique π with R ∼Θw [0,π] (p.43); under the axioms the infimum is that π (reading R1)
--   - encoding: α ∈ [0,1], π ∈ [0,1] and the sets of PSW6/PSW13 'are closed' → α, π : unitInterval; the sets are closed subsets of unitInterval; reason: [0,1] is closed in ℝ, so a subset of it is closed in [0,1] iff it is closed in ℝ
--   - encoding: Qw a σ-field → Qw a field (IsSetAlgebra) closed under countable unions; reason: the definition of a σ-field
--   - encoding: countably additive probability distribution → P(Θ) = 1, P ≥ 0 on Qw, and HasSum (fun i => P(R_i)) (P(⋃_i R_i)) for pairwise disjoint sequences of events; reason: HasSum of nonnegative terms is convergence of the series to the union's probability
--   - encoding: PSW7 for decreasing events Ri in Qw → PSW7 with the additional antecedent ⋂ Ri ∈ Qw; reason: for a σ-field the antecedent always holds, so this is the printed axiom
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), Lemma 1(b), p.23 (PDF p.24); proof p.44 (PDF p.45)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_calib
import Definitions.Def_ParallelSmallWorlds_SEU_LikelihoodAxioms
import Definitions.Def_ParallelSmallWorlds_SEU_CorrectionC1
import Definitions.Def_ParallelSmallWorlds_SEU_PSW7

namespace ParallelSmallWorlds.SEU

open SmallWorld

/-- **Lemma 1(b): countable additivity under Axiom PSW7.**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), Lemma 1(b), p.23 (PDF p.24), proved p.44 (PDF p.45): "if Qw is a σ-field,
then under Axioms PSW1—PSW7 there is a unique, countably additive probability distribution PΘw on
Θw agreeing with ⪰Θw in the sense that ∀R,S ∈ Qw, R ⪰Θw S ⟺ PΘw(R) ≥ PΘw(S)".

If `Qw` is a σ-field (a field closed under countable unions) and Axioms PSW1–PSW7 hold, with
`∅_Θ ∼ ∅_B` and correction C1, then the calibrated probability `P = calib W` satisfies

1. `P(Θ) = 1`, `P(R) ≥ 0` for events, and `Σ_i P(R_i) = P(⋃_i R_i)` (a convergent series)
   for every sequence of pairwise disjoint events (countable additivity);
2. `R ⪰Θw S ⟺ P(R) ≥ P(S)` for all events `R, S`;
3. `P` is the only function with `P'(R) ∈ [0,1]` and `R ∼Θw [0, P'(R)]` for every event `R`.

**Formalization Note.** Uniqueness is among functions calibrated on the reference experiment
(correction C3, see `lemma_1_a`). Countable additivity is `HasSum` of the sequence of
probabilities, which for nonnegative terms is convergence of the series to `P(⋃_i R_i)`. -/
theorem lemma_1_b {Θ C : Type*} (W : SmallWorld Θ C)
    (hQ : MeasureTheory.IsSetAlgebra W.Q)
    (hσ : ∀ R : ℕ → Set Θ, (∀ i, R i ∈ W.Q) → (⋃ i, R i) ∈ W.Q)
    (hL : LikelihoodAxioms W) (hC1 : CorrectionC1 W) (h7 : PSW7 W) :
    (calib W Set.univ = 1 ∧ (∀ R ∈ W.Q, 0 ≤ calib W R) ∧
      ∀ R : ℕ → Set Θ, (∀ i, R i ∈ W.Q) → Pairwise (Function.onFun Disjoint R) →
        HasSum (fun i => calib W (R i)) (calib W (⋃ i, R i))) ∧
    (∀ R ∈ W.Q, ∀ S ∈ W.Q, W.lik (Sum.inl R) (Sum.inl S) ↔ calib W S ≤ calib W R) ∧
    (∀ P : Set Θ → ℝ,
      (∀ R ∈ W.Q, P R ∈ Set.Icc (0 : ℝ) 1 ∧ W.indiffLik (Sum.inl R) (Sum.inr (Set.Icc 0 (P R)))) →
      ∀ R ∈ W.Q, P R = calib W R) := by sorry

end ParallelSmallWorlds.SEU

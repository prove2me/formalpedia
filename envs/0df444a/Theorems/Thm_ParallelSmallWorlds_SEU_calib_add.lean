-- Prove2me | Theorems.Thm_ParallelSmallWorlds_SEU_calib_add
-- name    : ParallelSmallWorlds.SEU.calib_add
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:47.241971+00:00
-- url     : https://prove2.me/theorems/94a8258f-02f2-4381-b946-3dfbea3df66a
-- title:
--   Additivity of the calibrated probability, eqs. (12)–(13) (corrected: strict form of PSW5(b))
-- statement:
--   Let a small world have a field of events $Q$ and satisfy Axioms PSW1–PSW6 (with the two empty events identified) and the strict form C1 of Axiom PSW5(b). Then the calibrated probability $P_\Theta$ is additive:
--
--   1. for disjoint events $R,S$,
--   $$P_\Theta(R\cup S)=P_\Theta(R)+P_\Theta(S);$$
--   2. for pairwise disjoint events $R_1,\dots,R_n$,
--   $$P_\Theta\Bigl(\bigcup_{i=1}^n R_i\Bigr)=\sum_{i=1}^n P_\Theta(R_i).$$
--
--   This is the step of the proof of Lemma 1 that makes the calibrated probability a finitely additive probability.
--
--   Differences from the source:
--   - correction: PSW5(b) with weak conclusions only (p.21) → also the strict form (structure CorrectionC1): R ⪰ E, S ⪰ F with one strict gives R ∪ S ≻ E ∪ F, and dually; reason: the proof's step (12) uses 'the implication of PSW5 for strictly more likely'; without it the statement is false: Θ = {a,b}, events ranked by v(∅)=0, v{a}=v{b}=0.6, v(Θ)=1, reference events by Lebesgue measure, satisfies PSW1–PSW8 as printed, yet π{a}+π{b} = 1.2 ≠ 1 = πΘ
--   - encoding: ∀ w = 1,2,…,W (each small world separately) → one arbitrary small world W : SmallWorld Θ C; reason: every hypothesis and every conclusion concerns a single world; the statement for an arbitrary world is the statement for each w
--   - encoding: ⪰Θw on the set union Qw ∪ B, in which ∅ is a single element → lik on the disjoint sum Set Θ ⊕ Set ℝ, with ∅_Θ ∼Θw ∅_B imposed (field empty_identified of LikelihoodAxioms); reason: the disjoint sum has two copies of ∅; identifying them restores the paper's single empty set (reading R6), which step (10) uses
--   - generalization: set union Qw ∪ B (an event of Θw equal as a set to a reference event is the same element) → disjoint sum: events of Θ are never identified with reference events; reason: only a weaker hypothesis: a relation on the set union pulls back to one on the disjoint sum satisfying every axiom, so the Lean statement specializes to the paper's
--   - reading: B, 'the σ-field of open and closed intervals on [0,1]'; PSW2 for 'intervals, open or closed' → RefEvents = measurable (Borel) subsets of [0,1]; PSW2 for [a,b] and (a,b), 0 ≤ a ≤ b ≤ 1, including the degenerate {a} and ∅; reason: a σ-field is read as the one these intervals generate (reading R5); half-open intervals are not added to PSW2, which would strengthen it
--   - reading: PΘw, the probability of Lemma 1 → calib W R = inf{π ∈ [0,1] | [0,π] ⪰Θw R}; reason: the proof defines PΘw(R) = πR, the unique π with R ∼Θw [0,π] (p.43); under the axioms the infimum is that π (reading R1)
--   - encoding: α ∈ [0,1], π ∈ [0,1] and the sets of PSW6/PSW13 'are closed' → α, π : unitInterval; the sets are closed subsets of unitInterval; reason: [0,1] is closed in ℝ, so a subset of it is closed in [0,1] iff it is closed in ℝ
--   - encoding: Qw a field → MeasureTheory.IsSetAlgebra W.Q (contains ∅, closed under complement and finite union); reason: the definition of a field of sets
--   - encoding: Ri, i = 1,…,n → R : Fin n → Set Θ, pairwise disjoint; n = 0 allowed (then the statement is P(∅) = 0); reason: indexing convention; the case n = 0 holds under the axioms
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), proof of Lemma 1(a), eqs. (12)–(13), pp.43–44 (PDF pp.44–45)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_calib
import Definitions.Def_ParallelSmallWorlds_SEU_LikelihoodAxioms
import Definitions.Def_ParallelSmallWorlds_SEU_CorrectionC1

namespace ParallelSmallWorlds.SEU

/-- **Additivity of the calibrated probability, eqs. (12)–(13).**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), proof of Lemma 1(a), eqs. (12)–(13), pp.43–44 (PDF pp.44–45): "Hence
PΘw(R ∪ S) = PΘw(R) + PΘw(S). Simple induction gives for Ri ∈ Qw, i = 1,2,…,n with
Ri ∩ Rj = ∅ for i ≠ j: PΘw(⋃_{i=1}^n Ri) = Σ_{i=1}^n PΘw(Ri)."

If `Qw` is a field and Axioms PSW1–PSW6 hold, with `∅_Θ ∼ ∅_B` and the strict form C1 of
PSW5(b), then (1) `calib W (R ∪ S) = calib W R + calib W S` for disjoint events `R, S`, and
(2) `calib W (⋃_{i<n} R_i) = Σ_{i<n} calib W R_i` for pairwise disjoint events `R_0, …, R_{n−1}`.

**Formalization Note.** Correction C1 (`CorrectionC1`) is the strict form of PSW5(b) that the
page's step (12) invokes; without it the statement is false (see `CorrectionC1`). The finite
family is indexed by `Fin n`; for `n = 0` the statement says `calib W ∅ = 0`. -/
theorem calib_add {Θ C : Type*} (W : SmallWorld Θ C)
    (hQ : MeasureTheory.IsSetAlgebra W.Q) (hL : LikelihoodAxioms W) (hC1 : CorrectionC1 W) :
    (∀ R ∈ W.Q, ∀ S ∈ W.Q, Disjoint R S → calib W (R ∪ S) = calib W R + calib W S) ∧
    (∀ (n : ℕ) (R : Fin n → Set Θ), (∀ i, R i ∈ W.Q) → Pairwise (Function.onFun Disjoint R) →
      calib W (⋃ i, R i) = ∑ i, calib W (R i)) := by sorry

end ParallelSmallWorlds.SEU

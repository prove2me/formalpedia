-- Prove2me | Theorems.Thm_ParallelSmallWorlds_SEU_lemma_1_c
-- name    : ParallelSmallWorlds.SEU.lemma_1_c
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:56.284011+00:00
-- url     : https://prove2.me/theorems/a3533808-db31-46e0-bc84-2c85bb28f9cc
-- title:
--   Lemma 1(c): conditional likelihood is represented by conditional probability
-- statement:
--   Let a small world have a field of events $Q$ and satisfy Axioms PSW1–PSW6 and PSW8 (with the two empty events identified), and let $P=P_\Theta$ be the calibrated probability. Then for all events $R,S,T$ with $T\succ_\Theta\emptyset$: $P(T)>0$, and
--
--   $$(R\mid T)\succeq_\Theta(S\mid T)\iff P(R\mid T)\ge P(S\mid T),$$
--
--   where $P(R\mid T)=P(R\cap T)/P(T)$.
--
--   This is the part of the paper that justifies Bayesian updating: conditional likelihood judgements are represented by conditional probabilities.
--
--   Differences from the source:
--   - encoding: ∀ w = 1,2,…,W (each small world separately) → one arbitrary small world W : SmallWorld Θ C; reason: every hypothesis and every conclusion concerns a single world; the statement for an arbitrary world is the statement for each w
--   - encoding: ⪰Θw on the set union Qw ∪ B, in which ∅ is a single element → lik on the disjoint sum Set Θ ⊕ Set ℝ, with ∅_Θ ∼Θw ∅_B imposed (field empty_identified of LikelihoodAxioms); reason: the disjoint sum has two copies of ∅; identifying them restores the paper's single empty set (reading R6), which step (10) uses
--   - generalization: set union Qw ∪ B (an event of Θw equal as a set to a reference event is the same element) → disjoint sum: events of Θ are never identified with reference events; reason: only a weaker hypothesis: a relation on the set union pulls back to one on the disjoint sum satisfying every axiom, so the Lean statement specializes to the paper's
--   - reading: B, 'the σ-field of open and closed intervals on [0,1]'; PSW2 for 'intervals, open or closed' → RefEvents = measurable (Borel) subsets of [0,1]; PSW2 for [a,b] and (a,b), 0 ≤ a ≤ b ≤ 1, including the degenerate {a} and ∅; reason: a σ-field is read as the one these intervals generate (reading R5); half-open intervals are not added to PSW2, which would strengthen it
--   - reading: PΘw, the probability of Lemma 1 → calib W R = inf{π ∈ [0,1] | [0,π] ⪰Θw R}; reason: the proof defines PΘw(R) = πR, the unique π with R ∼Θw [0,π] (p.43); under the axioms the infimum is that π (reading R1)
--   - encoding: α ∈ [0,1], π ∈ [0,1] and the sets of PSW6/PSW13 'are closed' → α, π : unitInterval; the sets are closed subsets of unitInterval; reason: [0,1] is closed in ℝ, so a subset of it is closed in [0,1] iff it is closed in ℝ
--   - encoding: Qw a field → MeasureTheory.IsSetAlgebra W.Q (contains ∅, closed under complement and finite union); reason: the definition of a field of sets
--   - encoding: PΘw(R | T) → calib W (R ∩ T) / calib W T, with 0 < calib W T in the conclusion; reason: the definition of conditional probability; positivity, the proof's first sentence, rules out division by zero
--   - reading: 'if, in addition, Axiom PSW8 holds' (in addition to the hypotheses of (a) or (b)) → Qw a field, PSW1–PSW6 and PSW8; reason: the hypotheses of part (a) plus PSW8; the strict form C1 is not needed, since positivity and agreement use only (9)–(10) and PSW2
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), Lemma 1(c), p.23 (PDF p.24); proof p.44 (PDF p.45)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_calib
import Definitions.Def_ParallelSmallWorlds_SEU_LikelihoodAxioms
import Definitions.Def_ParallelSmallWorlds_SEU_PSW8

namespace ParallelSmallWorlds.SEU

open SmallWorld

/-- **Lemma 1(c): conditional likelihood is represented by conditional probability.**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), Lemma 1(c), p.23 (PDF p.24), proved p.44 (PDF p.45): "if, in addition,
Axiom PSW8 holds, then ∀R,S,T ∈ Qw for which T ≻Θw ∅, (R | T) ⪰Θw (S | T) ⟺
PΘw(R | T) ≥ PΘw(S | T)."

If `Qw` is a field and Axioms PSW1–PSW6 and PSW8 hold, with `∅_Θ ∼ ∅_B`, then for
events `R, S, T` with `T ≻Θw ∅`: `P(T) > 0`, and `(R | T) ⪰Θw (S | T)` if and only if
`P(R ∩ T)/P(T) ≥ P(S ∩ T)/P(T)`, where `P = calib W`.

**Formalization Note.** `P(R | T)` is the quotient `P(R ∩ T)/P(T)`; the positivity `P(T) > 0`,
the first sentence of the proof, is part of the conclusion, so the quotient is never a division
by zero. Correction C1 is not needed here: positivity and the agreement of `P` with `⪰Θw` use
only the calibration (9)–(10) and Axiom PSW2. -/
theorem lemma_1_c {Θ C : Type*} (W : SmallWorld Θ C)
    (hQ : MeasureTheory.IsSetAlgebra W.Q) (hL : LikelihoodAxioms W) (h8 : PSW8 W) :
    ∀ R ∈ W.Q, ∀ S ∈ W.Q, ∀ T ∈ W.Q, W.strictLik (Sum.inl T) (Sum.inl ∅) →
      0 < calib W T ∧
      (W.condLik R S T ↔ calib W (S ∩ T) / calib W T ≤ calib W (R ∩ T) / calib W T) := by sorry

end ParallelSmallWorlds.SEU

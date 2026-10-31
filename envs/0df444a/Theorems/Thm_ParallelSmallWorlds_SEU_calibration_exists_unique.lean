-- Prove2me | Theorems.Thm_ParallelSmallWorlds_SEU_calibration_exists_unique
-- name    : ParallelSmallWorlds.SEU.calibration_exists_unique
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:18.140821+00:00
-- url     : https://prove2.me/theorems/5dff1cb4-6db8-4a5c-b128-1b9c4487c493
-- title:
--   Calibration of an event: $R\sim_{\Theta_w}[0,\pi_R]$ for a unique $\pi_R$ (eqs. (9)–(10))
-- statement:
--   Let a small world have a field of events $Q$ and satisfy Axioms PSW1–PSW6 (with the empty event of $\Theta$ and the empty reference event identified). Then for every event $R\in Q$ the calibrated probability $P_\Theta(R)$ lies in $[0,1]$,
--
--   $$R\sim_\Theta[0,P_\Theta(R)],$$
--
--   and $P_\Theta(R)$ is the only $\pi\in[0,1]$ with $R\sim_\Theta[0,\pi]$.
--
--   This is the first step of the proof of Lemma 1: every event of every small world is matched by an event of the common reference experiment, which is what makes probabilities comparable across worlds.
--
--   Differences from the source:
--   - encoding: ∀ w = 1,2,…,W (each small world separately) → one arbitrary small world W : SmallWorld Θ C; reason: every hypothesis and every conclusion concerns a single world; the statement for an arbitrary world is the statement for each w
--   - encoding: ⪰Θw on the set union Qw ∪ B, in which ∅ is a single element → lik on the disjoint sum Set Θ ⊕ Set ℝ, with ∅_Θ ∼Θw ∅_B imposed (field empty_identified of LikelihoodAxioms); reason: the disjoint sum has two copies of ∅; identifying them restores the paper's single empty set (reading R6), which step (10) uses
--   - generalization: set union Qw ∪ B (an event of Θw equal as a set to a reference event is the same element) → disjoint sum: events of Θ are never identified with reference events; reason: only a weaker hypothesis: a relation on the set union pulls back to one on the disjoint sum satisfying every axiom, so the Lean statement specializes to the paper's
--   - reading: B, 'the σ-field of open and closed intervals on [0,1]'; PSW2 for 'intervals, open or closed' → RefEvents = measurable (Borel) subsets of [0,1]; PSW2 for [a,b] and (a,b), 0 ≤ a ≤ b ≤ 1, including the degenerate {a} and ∅; reason: a σ-field is read as the one these intervals generate (reading R5); half-open intervals are not added to PSW2, which would strengthen it
--   - reading: PΘw, the probability of Lemma 1 → calib W R = inf{π ∈ [0,1] | [0,π] ⪰Θw R}; reason: the proof defines PΘw(R) = πR, the unique π with R ∼Θw [0,π] (p.43); under the axioms the infimum is that π (reading R1)
--   - encoding: α ∈ [0,1], π ∈ [0,1] and the sets of PSW6/PSW13 'are closed' → α, π : unitInterval; the sets are closed subsets of unitInterval; reason: [0,1] is closed in ℝ, so a subset of it is closed in [0,1] iff it is closed in ℝ
--   - encoding: Qw a field → MeasureTheory.IsSetAlgebra W.Q (contains ∅, closed under complement and finite union); reason: the definition of a field of sets
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), proof of Lemma 1(a), eqs. (9)–(10), p.43 (PDF p.44)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_calib
import Definitions.Def_ParallelSmallWorlds_SEU_LikelihoodAxioms

namespace ParallelSmallWorlds.SEU

open SmallWorld

/-- **Calibration of an event on the reference experiment, eqs. (9)–(10).**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), proof of Lemma 1(a), eqs. (9)–(10), p.43 (PDF p.44): "Hence ∃πR ∈ [0,1]
such that R ∼Θw [0,πR]. By PSW1 and PSW2, πR is unique."

If `Qw` is a field and Axioms PSW1–PSW6 hold (with the identification `∅_Θ ∼ ∅_B`), then for
every event `R ∈ Qw` the number `calib W R` lies in `[0,1]`, `R ∼Θw [0, calib W R]`, and it is
the only `π ∈ [0,1]` with `R ∼Θw [0,π]`. -/
theorem calibration_exists_unique {Θ C : Type*} (W : SmallWorld Θ C)
    (hQ : MeasureTheory.IsSetAlgebra W.Q) (hL : LikelihoodAxioms W) :
    ∀ R ∈ W.Q, calib W R ∈ Set.Icc (0 : ℝ) 1 ∧
      W.indiffLik (Sum.inl R) (Sum.inr (Set.Icc 0 (calib W R))) ∧
      ∀ π ∈ Set.Icc (0 : ℝ) 1, W.indiffLik (Sum.inl R) (Sum.inr (Set.Icc 0 π)) →
        π = calib W R := by sorry

end ParallelSmallWorlds.SEU

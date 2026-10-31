-- Prove2me | Theorems.Thm_ParallelSmallWorlds_SEU_calib_mono
-- name    : ParallelSmallWorlds.SEU.calib_mono
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:29.051399+00:00
-- url     : https://prove2.me/theorems/40afd4fd-8f59-49a0-b215-90118a732e51
-- title:
--   Monotonicity: $R\subseteq S\Rightarrow S\succeq_{\Theta_w}R$ and $P_{\Theta_w}(R)\le P_{\Theta_w}(S)$ (eq. (11))
-- statement:
--   Let a small world have a field of events $Q$ and satisfy Axioms PSW1–PSW6 (with the two empty events identified). Then for events $R\subseteq S$,
--
--   $$S\succeq_\Theta R\qquad\text{and}\qquad P_\Theta(R)\le P_\Theta(S),$$
--
--   where $P_\Theta$ is the calibrated probability.
--
--   This is the monotonicity step of the proof of Lemma 1, used before additivity is established.
--
--   Differences from the source:
--   - encoding: ∀ w = 1,2,…,W (each small world separately) → one arbitrary small world W : SmallWorld Θ C; reason: every hypothesis and every conclusion concerns a single world; the statement for an arbitrary world is the statement for each w
--   - reading: R ⊂ S → R ⊆ S; reason: the case R = S is trivial and the step is used for inclusion
--   - encoding: ⪰Θw on the set union Qw ∪ B, in which ∅ is a single element → lik on the disjoint sum Set Θ ⊕ Set ℝ, with ∅_Θ ∼Θw ∅_B imposed (field empty_identified of LikelihoodAxioms); reason: the disjoint sum has two copies of ∅; identifying them restores the paper's single empty set (reading R6), which step (10) uses
--   - generalization: set union Qw ∪ B (an event of Θw equal as a set to a reference event is the same element) → disjoint sum: events of Θ are never identified with reference events; reason: only a weaker hypothesis: a relation on the set union pulls back to one on the disjoint sum satisfying every axiom, so the Lean statement specializes to the paper's
--   - reading: B, 'the σ-field of open and closed intervals on [0,1]'; PSW2 for 'intervals, open or closed' → RefEvents = measurable (Borel) subsets of [0,1]; PSW2 for [a,b] and (a,b), 0 ≤ a ≤ b ≤ 1, including the degenerate {a} and ∅; reason: a σ-field is read as the one these intervals generate (reading R5); half-open intervals are not added to PSW2, which would strengthen it
--   - reading: PΘw, the probability of Lemma 1 → calib W R = inf{π ∈ [0,1] | [0,π] ⪰Θw R}; reason: the proof defines PΘw(R) = πR, the unique π with R ∼Θw [0,π] (p.43); under the axioms the infimum is that π (reading R1)
--   - encoding: α ∈ [0,1], π ∈ [0,1] and the sets of PSW6/PSW13 'are closed' → α, π : unitInterval; the sets are closed subsets of unitInterval; reason: [0,1] is closed in ℝ, so a subset of it is closed in [0,1] iff it is closed in ℝ
--   - encoding: Qw a field → MeasureTheory.IsSetAlgebra W.Q (contains ∅, closed under complement and finite union); reason: the definition of a field of sets
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), proof of Lemma 1(a), eq. (11), p.43 (PDF p.44)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_calib
import Definitions.Def_ParallelSmallWorlds_SEU_LikelihoodAxioms

namespace ParallelSmallWorlds.SEU

/-- **Monotonicity of likelihood and of the calibrated probability, eq. (11).**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), proof of Lemma 1(a), eq. (11), p.43 (PDF p.44): "So R ⊂ S ⟹ S ⪰θw R,
which implies PΘw(S) ≥ PΘw(R)."

If `Qw` is a field and Axioms PSW1–PSW6 hold (with `∅_Θ ∼ ∅_B`), then for events `R ⊆ S`,
`S ⪰Θw R` and `calib W R ≤ calib W S`.

**Formalization Note.** The page's `R ⊂ S` is read as inclusion `R ⊆ S` (the case `R = S` is
trivial). -/
theorem calib_mono {Θ C : Type*} (W : SmallWorld Θ C)
    (hQ : MeasureTheory.IsSetAlgebra W.Q) (hL : LikelihoodAxioms W) :
    ∀ R ∈ W.Q, ∀ S ∈ W.Q, R ⊆ S → W.lik (Sum.inl S) (Sum.inl R) ∧ calib W R ≤ calib W S := by sorry

end ParallelSmallWorlds.SEU

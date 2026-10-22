-- Prove2me | Theorems.Thm_QMaxCutBeyond_TwoQubit_lemma_2
-- name    : QMaxCutBeyond.TwoQubit.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:22.397625+00:00
-- url     : https://prove2.me/theorems/658661f6-963d-4855-8562-0c0231bc9e70
-- title:
--   Lemma 2 — a matching M and a forest F with Σ_v max_{e∼v} w_e = Σ_{e∈M} w_e + Σ_{e∈F} w_e
-- statement:
--   Let $G=(V,E,w)$ be a graph with nonnegative weights. There are edge subsets $M,F\subseteq E$ such that $M$ is a matching, $F$ is a forest (the graph on $V$ with edge set $F$ has no cycle), and
--   $$\sum_{v\in V}\max_{e\sim v}w_e=\sum_{e\in M}w_e+\sum_{e\in F}w_e .$$
--
--   The lemma refines the naive bound $\sum_v\max_{e\sim v}w_e\le2W$; it is what lets the two entangled and classical candidate states of eqs. (25)–(26) beat $1/2$.
--
--   **Formalization Note** Only existence is stated; the paper's "we may efficiently compute" is not formalized. An isolated vertex contributes $0$ to the left-hand side.
-- source:
--   Anshu, Gosset & Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394v1, p. 10, Lemma 2

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace QMaxCutBeyond.TwoQubit

/-- Lemma 2, p. 10 (existence part): there are edge subsets `M, F ⊆ E` with `M` a matching and
`F` a forest such that `Σ_{v∈V} max_{e∼v} w_e = Σ_{e∈M} w_e + Σ_{e∈F} w_e`. -/
theorem lemma_2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e) :
    ∃ M F : Finset (Sym2 (Fin n)), M ⊆ G.edgeFinset ∧ F ⊆ G.edgeFinset ∧
      IsEdgeMatching M ∧ (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).IsAcyclic ∧
      ∑ v, maxIncident G w v = ∑ e ∈ M, w e + ∑ e ∈ F, w e := by sorry

end QMaxCutBeyond.TwoQubit

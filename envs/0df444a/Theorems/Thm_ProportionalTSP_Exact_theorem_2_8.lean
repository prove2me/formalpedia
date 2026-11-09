-- Prove2me | Theorems.Thm_ProportionalTSP_Exact_theorem_2_8
-- name    : ProportionalTSP.Exact.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:43.499075+00:00
-- url     : https://prove2.me/theorems/530605d6-f545-4074-ba08-e1c0ddded66e
-- title:
--   Theorem 2.8 — Every optimal tour contains a minimum-load assignment
-- statement:
--   Under the section's graph assumptions, let $H$ be a minimum-cost tour. There are prices $a\in\mathbb R^L$ with
--   $$\forall r\in R\quad \exists l\in L:\ lr\in H\cap F(a).$$
--   Consequently $H$ contains an assignment $A$ that is tight and minimum-cost for its load. If $w$ is generic, this same assignment has balanced load and equals the canonical $A_{d^A}$. The price and minimum-assignment clauses hold without genericity. This is the structural link between tour optimization and assignment enumeration.
--
--   Differences from the source:
--   - encoding: finite labeled vertices and assignments on L and R → Fin-indexed vertices, with paper index equal to Lean index plus one; reason: relabeling preserves every finite instance; section hypotheses remain explicit
--   - encoding: Hamiltonian cycles counted as undirected cycles → finite unordered edge sets represented by a spanning simple cyclic list of length at least three; reason: rotations and reversal identify the same cycle, including in the parity count
--   - encoding: the unique minimum-cost assignment for generic costs → a finite argmin with least base-m assignment-rank tie rule, and a default only at infeasible loads; reason: the uniqueness clause is proved in Lemma 2.6; all theorem uses of canonical assignments have feasible loads
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Theorem 2.8, PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Symbolic

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

theorem theorem_2_8 {m k : ℕ} [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (G : SimpleGraph (Vertex m k)) (hG : SectionGraph G)
    (w : Sym2 (Vertex m k) → ℝ) (H : Finset (Sym2 (Vertex m k)))
    (hH : OptimalTour G w H) :
    ∃ a : Fin m → ℝ,
      (∀ r, ∃ l, s(Sum.inl l, Sum.inr r) ∈ H ∧ TightEdge (cross w) a Finset.univ l r) ∧
      ∃ A : Assignment m k,
        (∀ r, s(Sum.inl (A r), Sum.inr r) ∈ H) ∧ TightAssignment (cross w) a A ∧
        MinimumAssignment (cross w) (load A) A ∧
        (Generic (cross w) → balanced (load A) ∧ A = canonical (cross w) (load A)) := by sorry

end ProportionalTSP.Exact

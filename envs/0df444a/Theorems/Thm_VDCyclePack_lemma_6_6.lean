-- Prove2me | Theorems.Thm_VDCyclePack_lemma_6_6
-- name    : VDCyclePack.lemma_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:55.151286+00:00
-- url     : https://prove2.me/theorems/09297630-deca-4342-bdec-847e029f63ef
-- title:
--   Lemma 6.6: under (3), $\beta$ of a union of $t$ candidates is at most $3ct+\frac{32t}{a}(\log(t+2)+5)$
-- statement:
--   Let $H$ be a marked packing of a finite graph $G$, $A=V(H)$, and let $a\ge2$, $L\ge3$, $c\ge1$ be integers. Assume (3): every cycle of $G$ of length at most $aL$ meets $A$. If $U$ is the union of $t$ distinct members of $\mathcal C(H,L,c)$, then
--   $$
--   \beta(U)\le 3ct+\frac{32t}{a}\bigl(\log_2(t+2)+5\bigr).
--   $$
--
--   This is property 2 of Lemma 4.3, hence the structural hypothesis of Theorem 4.2 with $\alpha=3c+160/a$ and $\gamma=32/a$.
--
--   **Formalization Note** "$t$ distinct members" is a set $R\subseteq\mathcal C(H,L,c)$ with $t=|R|$, and $U$ is its union.
--
--   Differences from the source:
--   - encoding: a marked packing H, A = V(H), A-paths in G − E(H) → H = P.sup id for a cycle packing P (a Finset of pairwise vertex-disjoint cycle subgraphs); A = H.verts; A-paths are IsAPath in G.deleteEdges H.edgeSet; reason: the paper's definitions (pp.10–11); same instances
--   - encoding: c_H(C), C(H, L, c), n = |V(G)| → contacts (components of the subgraph meet C ⊓ H), candidates G H L c, Fintype.card V; reason: the paper's definitions (pp.10, 13); same instances
--   - encoding: assume (3): every cycle of G of length at most aL meets A, and girth(G − A) > aL → ShortCyclesMeet G H a L; reason: the paper's 'Equivalently' form of (3) (p.18)
--   - encoding: U the union of t distinct members of C(H, L, c) → R ⊆ candidates G H L c with t = R.card and U = R.sup id; reason: same statement
--   - encoding: β(⋃_{C∈R} C), log → cycleRank (R.sup id), the minimum size of a feedback edge set of the union in the subgraph lattice; Real.logb 2; reason: the paper's definition of β (p.10), of unions (p.9) and of logarithms (base two, p.9)
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 6.6, p.20 ((3) on p.18; a, L, c from Section 6, p.17)

import Mathlib
import Definitions.Def_VDCyclePack_IsCyclePacking
import Definitions.Def_VDCyclePack_ShortCyclesMeet
import Definitions.Def_VDCyclePack_candidates
import Definitions.Def_VDCyclePack_cycleRank

namespace VDCyclePack

/-- **Lemma 6.6 (feedback edge sets of unions of candidates).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 6.6, p.20: "Assume (3). If U is the union of t distinct members of C(H, L, c),
then β(U) ≤ 3ct + (32t/a)(log(t + 2) + 5)." Condition (3), p.18: "every cycle of G of length at most
aL meets A, and girth(G − A) > aL." Here `H` is a marked packing, `A = V(H)`, and `a ≥ 2`, `L ≥ 3`,
`c ≥ 1` are integers (Section 6, p.17).

Let `P` be a cycle packing of `G`, `H = ⋃ P`, and integers `a ≥ 2`, `L ≥ 3`, `c ≥ 1` such that every
cycle of `G` of length at most `aL` meets `V(H)`. Then for every set `R` of `t` candidates in
`𝒞(H, L, c)`, the union `U` of the members of `R` has `β(U) ≤ 3ct + (32t/a)(log₂(t + 2) + 5)`.

**Formalization Note.** (3) is `ShortCyclesMeet`; β is the minimum feedback edge set
(`cycleRank`); "t distinct members" is a subset `R` of the candidate family with `t = |R|`. -/
theorem lemma_6_6 {V : Type*} [Fintype V] (G : SimpleGraph V) (P : Finset G.Subgraph)
    (hP : IsCyclePacking P) (a L c : ℕ) (ha : 2 ≤ a) (hL : 3 ≤ L) (hc : 1 ≤ c)
    (h3 : ShortCyclesMeet G (P.sup id) a L) :
    ∀ R ⊆ candidates G (P.sup id) L c,
      (cycleRank (R.sup id) : ℝ) ≤
        3 * c * R.card + 32 * R.card / a * (Real.logb 2 (R.card + 2) + 5) := by sorry

end VDCyclePack

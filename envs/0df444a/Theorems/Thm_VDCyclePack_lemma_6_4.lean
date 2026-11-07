-- Prove2me | Theorems.Thm_VDCyclePack_lemma_6_4
-- name    : VDCyclePack.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:47.253007+00:00
-- url     : https://prove2.me/theorems/88036587-af01-4406-962f-125b2f0d4082
-- title:
--   Lemma 6.4: $c_H(C)\le2|V(C)\cap X|+1$, and the weight outside $\mathcal C(H,L,c)$ is at most $n/(L+1)+(4M+T)/(c+1)$
-- statement:
--   Let $H$ be a marked packing of a finite graph $G$ with $n$ vertices, $A=V(H)$, $A$-paths taken in $G-E(H)$, and let $M\ge1$, $L\ge3$, $c\ge1$ be integers. Suppose that a set $X$ of at most $2M-2$ vertices meets every $A$-path. Then every cycle $C$ satisfies
--   $$
--   c_H(C)\le 2|V(C)\cap X|+1,
--   $$
--   and consequently, in every fractional packing of value $T$, the cycles not in $\mathcal C(H,L,c)$ have total weight at most
--   $$
--   \frac{n}{L+1}+\frac{4M+T}{c+1}.
--   $$
--
--   With Proposition 6.3 this gives property 1 of Lemma 4.3.
--
--   **Formalization Note** The statement is given for every integer $M\ge1$; the paper's $M=8q\lceil\log_2(q+2)\rceil$ is a special case.
--
--   Differences from the source:
--   - generalization: M = 8q⌈log(q + 2)⌉ for the section's q ≥ 2 → any integer M ≥ 1; reason: the statement for M = bigM q is the paper's; the lemma uses only |X| ≤ 2M − 2
--   - encoding: a marked packing H, A = V(H), A-paths in G − E(H) → H = P.sup id for a cycle packing P (a Finset of pairwise vertex-disjoint cycle subgraphs); A = H.verts; A-paths are IsAPath in G.deleteEdges H.edgeSet; reason: the paper's definitions (pp.10–11); same instances
--   - encoding: c_H(C), C(H, L, c), n = |V(G)| → contacts (components of the subgraph meet C ⊓ H), candidates G H L c, Fintype.card V; reason: the paper's definitions (pp.10, 13); same instances
--   - encoding: in every fractional packing of value T, the total weight of the cycles not in C(H, L, c) → ∀ x with IsFracPacking G x, the sum of x C over cycles G \ candidates, with T = value G x; reason: same statement; x is read only on cycles
--   - encoding: |V(C) ∩ X| → (X.filter (· ∈ C.verts)).card; reason: same number
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 6.4, p.19

import Mathlib
import Definitions.Def_VDCyclePack_IsCyclePacking
import Definitions.Def_VDCyclePack_MeetsAllAPaths
import Definitions.Def_VDCyclePack_contacts
import Definitions.Def_VDCyclePack_candidates
import Definitions.Def_VDCyclePack_IsFracPacking
import Definitions.Def_VDCyclePack_value

namespace VDCyclePack

open Classical in
/-- **Lemma 6.4 (weight outside the candidate family).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 6.4, p.19: "Suppose that a set X of at most 2M − 2 vertices meets every A-path.
Then every cycle C satisfies c_H(C) ≤ 2|V(C) ∩ X| + 1. Consequently, in every fractional packing of
value T, the cycles not in C(H, L, c) have total weight at most n/(L + 1) + (4M + T)/(c + 1)."
Here `H` is a marked packing, `A = V(H)`, A-paths lie in `G − E(H)`, `L ≥ 3`, `c ≥ 1`.

Let `P` be a cycle packing of `G`, `H = ⋃ P`, `A = V(H)`, let `M ≥ 1`, `L ≥ 3`, `c ≥ 1` be integers and
let `X` be a set of at most `2M − 2` vertices meeting every A-path of `G − E(H)`. Then every cycle `C`
of `G` has `c_H(C) ≤ 2|V(C) ∩ X| + 1`, and for every fractional packing `x` of `G`, of value `T`, the
cycles outside `𝒞(H, L, c)` carry total weight at most `n/(L + 1) + (4M + T)/(c + 1)`.

**Formalization Note.** The paper's `M` is `8q⌈log(q + 2)⌉` for the section's `q ≥ 2`; the statement is
given for every integer `M ≥ 1`, which contains that case. -/
theorem lemma_6_4 {V : Type*} [Fintype V] (G : SimpleGraph V) (P : Finset G.Subgraph)
    (hP : IsCyclePacking P) (M L c : ℕ) (hM : 1 ≤ M) (hL : 3 ≤ L) (hc : 1 ≤ c) (X : Finset V)
    (hX : X.card ≤ 2 * M - 2)
    (hmeet : MeetsAllAPaths (G.deleteEdges (P.sup id).edgeSet) (P.sup id).verts X) :
    (∀ C ∈ cycles G, contacts (P.sup id) C ≤ 2 * (X.filter fun w => w ∈ C.verts).card + 1) ∧
    ∀ x : G.Subgraph → ℝ, IsFracPacking G x →
      ∑ C ∈ cycles G \ candidates G (P.sup id) L c, x C ≤
        (Fintype.card V : ℝ) / (L + 1) + (4 * M + value G x) / (c + 1) := by sorry

end VDCyclePack

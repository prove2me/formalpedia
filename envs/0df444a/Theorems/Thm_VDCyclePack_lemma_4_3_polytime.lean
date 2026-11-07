-- Prove2me | Theorems.Thm_VDCyclePack_lemma_4_3_polytime
-- name    : VDCyclePack.lemma_4_3_polytime
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:49.628818+00:00
-- url     : https://prove2.me/theorems/cc94865d-38e2-4920-96ae-9b060bef37f6
-- title:
--   Lemma 4.3 (Structure), polynomial-time part: the $q$ cycles or the marked packing are found in polynomial time (existence: lemma_4_3)
-- statement:
--   There is a polynomial-time algorithm that, given a finite simple graph $G$ on $n$ vertices and integers $q\ge2$, $a\ge2$, $L\ge3$, $c\ge1$ (in binary), with $M=8q\lceil\log_2(q+2)\rceil$, either returns $q$ vertex-disjoint cycles of $G$, or returns a family of pairwise vertex-disjoint cycles whose union $H$ is a marked packing with properties 1 and 2 of Lemma 4.3:
--
--   1. in every fractional packing of $G$ of value $T$, the cycles outside $\mathcal C(H,L,c)$ have total weight at most $\frac{n}{L+1}+\frac{4M+T}{c+1}$;
--   2. for every $R\subseteq\mathcal C(H,L,c)$ with $t=|R|$, $\beta(\bigcup_{C\in R}C)\le 3ct+\frac{32t}{a}(\log_2(t+2)+5)$.
--
--   This is the "in polynomial time, one can either find" clause of Lemma 4.3; the existence part is `VDCyclePack.lemma_4_3`.
--
--   **Formalization Note** A Mathlib `TM2` machine on (encoded graph, $q$, $a$, $L$, $c$); its output is a tagged list of vertex lists (tag $0$: the $q$ cycles; tag $1$: the marked cycles). Properties 1–2 use the same predicates as `lemma_4_3`, on the decoded graph and the decoded marked packing.
--
--   Differences from the source:
--   - reading: in polynomial time, one can either find q vertex-disjoint cycles in G, or find a marked packing H with properties 1–2 → ∃ alg with Nonempty (Turing.TM2ComputableInPolyTime (encGraph ++ words of q, a, L, c) (tagged encCycles) alg), output Sum.inl cs (q cycles) or Sum.inr hs (the marked cycles), correct whenever q ≥ 2, a ≥ 2, L ≥ 3, c ≥ 1; reason: the standard Turing-machine reading: Mathlib's TM2 machines are deterministic, numbers are written in binary, and the machine must halt in polynomial time on every input while its output is constrained only on inputs meeting the hypotheses
--   - encoding: a finite simple undirected graph G given as input → a GraphInst (n and a list of index pairs) read through GraphInst.toGraph on Fin n; loops, repeats, both orientations and out-of-range pairs are ignored, so no well-formedness hypothesis; reason: every finite simple graph is isomorphic to such a graph and the statement is invariant under relabelling; same instances
--   - encoding: q vertex-disjoint cycles; the marked packing H → cs: q pairwise disjoint IsCycleList vertex lists; hs: pairwise disjoint IsCycleList vertex lists with H = (familyOf I hs).sup id; reason: cycles given by their vertex sequences; disjoint lists are vertex-disjoint cycles; same instances
--   - encoding: c_H(C), C(H, L, c), n = |V(G)| → contacts (components of the subgraph meet C ⊓ H), candidates G H L c, Fintype.card V; reason: the paper's definitions (pp.10, 13); same instances
--   - encoding: in every fractional packing of value T, the total weight of the cycles not in C(H, L, c) → ∀ x with IsFracPacking G x, the sum of x C over cycles G \ candidates, with T = value G x; reason: same statement; x is read only on cycles
--   - encoding: β(⋃_{C∈R} C), log → cycleRank (R.sup id), the minimum size of a feedback edge set of the union in the subgraph lattice; Real.logb 2; reason: the paper's definition of β (p.10), of unions (p.9) and of logarithms (base two, p.9)
--   - generalization: polynomial in the size of the input graph, n = |V(G)| vertices included, for integers q, a, L, c → polynomial in the length of the word, where n is one binary number, so isolated vertices add no length, and q, a, L, c are binary numbers; reason: isolated vertices lie on no cycle or A-path, so a machine can ignore them and mention only indices of the edge list; a bound in the shorter word is in particular polynomial in the paper's size; the procedure of Section 6 selects at most n/3 cycles and only compares q and a·L with quantities at most n, so large parameters cost nothing
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 4.3, p.13

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_VDCyclePack_encWNat
import Definitions.Def_VDCyclePack_GraphInst_toGraph
import Definitions.Def_VDCyclePack_IsCycleList
import Definitions.Def_VDCyclePack_familyOf
import Definitions.Def_VDCyclePack_IsFracPacking
import Definitions.Def_VDCyclePack_value
import Definitions.Def_VDCyclePack_candidates
import Definitions.Def_VDCyclePack_cycleRank
import Definitions.Def_VDCyclePack_bigM
import Definitions.Def_VDCyclePack_encGraph
import Definitions.Def_VDCyclePack_encCycles

namespace VDCyclePack

open Classical in
/-- **Lemma 4.3 (structure), polynomial time.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 4.3, p.13: "In polynomial time, one can either find q vertex-disjoint cycles in
G, or find a marked packing H with the following properties." (properties 1 and 2 as in
`lemma_4_3`).

There is a map `alg`, computable by a Turing machine in time polynomial in the binary length of
its input `(I, q, a, L, c)`, such that whenever `q ≥ 2`, `a ≥ 2`, `L ≥ 3`, `c ≥ 1`: if it returns
`inl cs`, then `cs` is a list of `q` pairwise vertex-disjoint cycles of `I.toGraph`; if it returns
`inr hs`, then `hs` is a list of pairwise vertex-disjoint cycles whose union `H` satisfies items 1
and 2 of Lemma 4.3 (with `M = 8q⌈log₂(q+2)⌉` and `n = I.n`).

**Formalization Note.** Input encoding `encGraph` followed by the binary words of `q, a, L, c`;
output a tag symbol (`0` for cycles, `1` for a marked packing) followed by `encCycles`. Cycles are
vertex lists (`IsCycleList`); the marked packing is decoded by `familyOf`, and items 1–2 use the same
`IsFracPacking`, `value`, `candidates` and `cycleRank` as `lemma_4_3`. -/
theorem lemma_4_3_polytime :
    ∃ alg : GraphInst × ℕ × ℕ × ℕ × ℕ → List (List ℕ) ⊕ List (List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime
        (fun p : GraphInst × ℕ × ℕ × ℕ × ℕ => encGraph p.1 ++ encWNat p.2.1 ++ encWNat p.2.2.1 ++
          encWNat p.2.2.2.1 ++ encWNat p.2.2.2.2)
        (Sum.elim (fun cs => (0 : OnlineCRS.Combine.Sym) :: encCycles cs)
          (fun hs => (1 : OnlineCRS.Combine.Sym) :: encCycles hs)) alg) ∧
      ∀ (I : GraphInst) (q a L c : ℕ), 2 ≤ q → 2 ≤ a → 3 ≤ L → 1 ≤ c →
        Sum.elim
          (fun cs : List (List ℕ) => cs.length = q ∧ (∀ l ∈ cs, IsCycleList I l) ∧
            cs.Pairwise List.Disjoint)
          (fun hs : List (List ℕ) => (∀ l ∈ hs, IsCycleList I l) ∧ hs.Pairwise List.Disjoint ∧
            (∀ x : I.toGraph.Subgraph → ℝ, IsFracPacking I.toGraph x →
              ∑ C ∈ cycles I.toGraph \ candidates I.toGraph ((familyOf I hs).sup id) L c, x C ≤
                (I.n : ℝ) / (L + 1) + (4 * bigM q + value I.toGraph x) / (c + 1)) ∧
            ∀ R ⊆ candidates I.toGraph ((familyOf I hs).sup id) L c,
              (cycleRank (R.sup id) : ℝ) ≤
                3 * c * R.card + 32 * R.card / a * (Real.logb 2 (R.card + 2) + 5))
          (alg (I, q, a, L, c)) := by sorry

end VDCyclePack

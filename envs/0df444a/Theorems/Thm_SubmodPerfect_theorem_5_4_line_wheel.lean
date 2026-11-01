-- Prove2me | Theorems.Thm_SubmodPerfect_theorem_5_4_line_wheel
-- name    : SubmodPerfect.theorem_5_4_line_wheel
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:45.352979+00:00
-- url     : https://prove2.me/theorems/f122bdcf-f5fa-4a55-99d0-b4bcfd1cec2c
-- title:
--   Theorem 5.4 (corrected: the paths avoid $v$) — line wheels in (C4, prism)-free perfect graphs
-- statement:
--   Let $G$ be a (C4, prism)-free perfect graph and $(H,v)$ a line wheel of $G$ with $H=a\text{-}b\text{-}\cdots\text{-}c\text{-}d\text{-}\cdots\text{-}a$ and $N(v)\cap V(H)=\{a,b,c,d\}$. Let $P$ be the path of $H\setminus b$ from $a$ to $d$ and $Q$ the path of $H\setminus a$ from $b$ to $c$, with interiors $P^*=V(P)\setminus\{a,d\}$, $Q^*=V(Q)\setminus\{b,c\}$. Then
--
--   1. $v$ has a neighbour in every path of $G\setminus v$ from $P\setminus a$ to $Q\setminus c$, and in every path of $G\setminus v$ from $P\setminus d$ to $Q\setminus b$; and
--   2. $v$ breaks each of $\{a\}\cup Q^*$, $\{d\}\cup Q^*$, $\{b\}\cup P^*$ and $\{c\}\cup P^*$.
--
--   Together with Theorem 5.3 this handles every proper wheel in the proof of Theorem 5.6.
--
--   **Formalization Note** The cyclic order is encoded by the arcs: $P$ is an induced path inside $H$ from $a$ to $d$ avoiding $b,c$, $Q$ one from $b$ to $c$ avoiding $a,d$, and $ab$, $cd$ are edges.
--
--   Differences from the source:
--   - correction: v has a neighbour in every path from P \ a to Q \ c (and from P \ d to Q \ b) → every such path R with v ∉ R; reason: as printed it is false: v ∉ P ∪ Q and v is adjacent to d ∈ P \ a and b ∈ Q \ c, so the one-vertex path R = v is a path from P \ a to Q \ c in which v has no neighbour; such line wheels exist, e.g. a 10-hole 0-1-…-9-0 with v adjacent to 0, 1, 5, 6, which is C4-free, prism-free and Berge, hence perfect. The proof treats paths anticomplete to v, i.e. paths of G \ v
--   - encoding: H = a-b-…-c-d-…-a → P ⊆ H from a to d avoiding b, c, and Q ⊆ H from b to c avoiding a, d, with ab and cd edges; reason: these arcs exist exactly in that cyclic order; same instances
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Theorem 5.4, p.17

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Theorem 5.4, p.17 (corrected: the paths from `P \ a` to `Q \ c` avoid `v`).

Let `G` be a (C4, prism)-free perfect graph and `(H, v)` a line wheel with
`H = a-b-…-c-d-…-a` and `N(v) ∩ H = {a, b, c, d}`. Let `P` be the path in `H \ b` from `a` to `d`
and `Q` the path in `H \ a` from `b` to `c`. Then `v` has a neighbour in every path (of `G \ v`)
from `P \ a` to `Q \ c` and in every path from `P \ d` to `Q \ b`. In particular, `v` breaks
each of `{a} ∪ Q*`, `{d} ∪ Q*`, `{b} ∪ P*` and `{c} ∪ P*`.

**Formalization Note.** The cyclic order `a-b-…-c-d-…-a` is encoded by the arcs: `P` is an
induced path of `G` inside `H` from `a` to `d` avoiding `b` and `c`, and `Q` one from `b` to `c`
avoiding `a` and `d`, with `ab` and `cd` edges. The paths `R` in the first conclusion are
required to avoid `v`: as printed, the one-vertex path `R = v` is a path from `P \ a` to `Q \ c`
(`v` is adjacent to `d` and `b`) in which `v` has no neighbour. `P* = V(P) \ {a, d}`,
`Q* = V(Q) \ {b, c}`. -/
theorem theorem_5_4_line_wheel {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hperf : StrongPerfectGraph.Main.IsPerfect G) (hC4 : IsC4Free G) (hprism : IsPrismFree G)
    (H : List V) (v : V) (hline : IsLineWheel G H v) (a b c d : V)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hN : H.toFinset.filter (fun x => G.Adj v x) = {a, b, c, d})
    (P Q : List V) (hP : IsPathFrom G P a d) (hPH : ∀ x ∈ P, x ∈ H) (hbP : b ∉ P) (hcP : c ∉ P)
    (hQ : IsPathFrom G Q b c) (hQH : ∀ x ∈ Q, x ∈ H) (haQ : a ∉ Q) (hdQ : d ∉ Q) :
    (∀ R : List V, IsPathFromSetTo G (P.toFinset.erase a) (Q.toFinset.erase c) R → v ∉ R →
        ∃ x ∈ R, G.Adj v x) ∧
      (∀ R : List V, IsPathFromSetTo G (P.toFinset.erase d) (Q.toFinset.erase b) R → v ∉ R →
        ∃ x ∈ R, G.Adj v x) ∧
      BreaksIn G Finset.univ v (insert a (Q.toFinset \ {b, c})) ∧
      BreaksIn G Finset.univ v (insert d (Q.toFinset \ {b, c})) ∧
      BreaksIn G Finset.univ v (insert b (P.toFinset \ {a, d})) ∧
      BreaksIn G Finset.univ v (insert c (P.toFinset \ {a, d})) := by sorry

end SubmodPerfect

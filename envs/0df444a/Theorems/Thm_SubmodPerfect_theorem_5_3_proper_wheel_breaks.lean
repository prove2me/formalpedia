-- Prove2me | Theorems.Thm_SubmodPerfect_theorem_5_3_proper_wheel_breaks
-- name    : SubmodPerfect.theorem_5_3_proper_wheel_breaks
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:50.259149+00:00
-- url     : https://prove2.me/theorems/d4e7fafc-a066-4766-8524-64225dbcbf05
-- title:
--   Theorem 5.3 — a proper non-line wheel center breaks every red–blue pair
-- statement:
--   Let $G$ be a (C4, prism)-free perfect graph and $(H,v)$ a proper wheel of $G$ that is not a line wheel. Let $R,B$ be a bicoloring of $V(H)$ with $B\setminus N(v)\ne\emptyset$. Then
--
--   $$v\ \text{breaks}\ \{r,b\}\qquad\text{for every }r\in R\text{ and }b\in B\setminus N(v).$$
--
--   The paper derives this from Theorem 4.5 of Conforti, Cornuéjols and Vušković (*Square-free perfect graphs*, 2004); it is one of the three wheel theorems used for paws.
--
--   Differences from the source:
--   - encoding: a bicoloring of a proper wheel that is not odd → IsBicoloring, which includes that the wheel is proper and not odd; reason: the paper defines bicolorings only for such wheels; same instances
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Theorem 5.3, p.17 (from [6], Theorem 4.5)

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Theorem 5.3 (from Theorem 4.5 of Conforti–Cornuéjols–Vušković), p.17.

Let `G` be a (C4, prism)-free perfect graph and `(H, v)` a proper wheel in `G` that is not a
line wheel. Let `R, B` be a bicoloring of the vertices of `H` with `B \ N(v) ≠ ∅`. Then for every
`r ∈ R` and `b ∈ B \ N(v)`, `v` breaks `{r, b}`.

**Formalization Note.** `IsBicoloring` includes the paper's standing requirement that the wheel
is proper and not odd. "Breaks" is taken in `G`. -/
theorem theorem_5_3_proper_wheel_breaks {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hperf : StrongPerfectGraph.Main.IsPerfect G) (hC4 : IsC4Free G) (hprism : IsPrismFree G)
    (H : List V) (v : V) (hprop : IsProperWheel G H v) (hline : ¬ IsLineWheel G H v)
    (R B : Finset V) (hbic : IsBicoloring G H v R B) (hB : ∃ b ∈ B, ¬ G.Adj v b) :
    ∀ r ∈ R, ∀ b ∈ B, ¬ G.Adj v b → BreaksIn G Finset.univ v {r, b} := by sorry

end SubmodPerfect

-- Prove2me | Theorems.Thm_SubmodPerfect_theorem_5_5_twin_wheel
-- name    : SubmodPerfect.theorem_5_5_twin_wheel
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:47.323124+00:00
-- url     : https://prove2.me/theorems/cc26d903-cfd7-4ec1-83d5-21981089d0f5
-- title:
--   Theorem 5.5 — twin wheels: a star cutset separates $v$ or $u$ from the rest of the hole
-- statement:
--   Let $G$ be a (C4, prism)-free perfect graph and $(H,v)$ a twin wheel of $G$, with $a,u,b$ the neighbours of $v$ in $H$ in this order along $H$. Let $S_u=N[u]\setminus\{v\}$ and $S_v=N[v]\setminus\{u\}$. Then
--
--   1. either $S_u$ is a cutset of $G$ separating $v$ from a vertex of $H\setminus\{a,u,b\}$, or $S_v$ is a cutset of $G$ separating $u$ from a vertex of $H\setminus\{a,u,b\}$; and
--   2. either $u$ breaks $(H\setminus\{a,u,b\})\cup\{v\}$ or $v$ breaks $H\setminus\{a,b\}$.
--
--   This is the twin-wheel case of the paw theorem: with $v=b_2$, $u=b_1$ it gives "$b_2$ breaks $\{c,b_1\}$ or $b_1$ breaks $\{c,b_2\}$".
--
--   Differences from the source:
--   - reading: in particular, either u breaks H \ {a, b} or v breaks H \ {a, b} → either u breaks (H \ {a, u, b}) ∪ {v} or v breaks H \ {a, b}; reason: u ∈ H \ {a, b}, and breaking is defined only for a vertex outside the set (p.14); the u branch is read as the u–v mirror of the v branch, which is what case (i) gives and how the proof of Theorem 5.6 uses it. The alternative of dropping the domain condition makes the u branch vacuously true and the clause empty
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Theorem 5.5, p.18

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Theorem 5.5, p.18.

Let `G` be a (C4, prism)-free perfect graph and `(H, v)` a twin wheel in `G`. Let `a, u, b` be the
neighbours of `v` in `H` in this order along `H`. Let `S_u = N[u] \ {v}` and `S_v = N[v] \ {u}`.
Then (i) `S_u` is a cutset of `G` separating `v` from a vertex of `H \ {a, u, b}`, or (ii) `S_v` is
a cutset of `G` separating `u` from a vertex of `H \ {a, u, b}`. In particular, either `u`
breaks `(H \ {a, u, b}) ∪ {v}` or `v` breaks `H \ {a, b}`.

**Formalization Note.** "In this order" is `a-u` and `u-b` being edges of `H`. The printed
last sentence reads "either u breaks H \ {a, b} or v breaks H \ {a, b}"; since `u ∈ H \ {a, b}`
and breaking is defined only for a vertex outside the set (p.14), the `u` branch is read as the
`u`–`v` mirror of the `v` branch, which is what case (i) gives. -/
theorem theorem_5_5_twin_wheel {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hperf : StrongPerfectGraph.Main.IsPerfect G) (hC4 : IsC4Free G) (hprism : IsPrismFree G)
    (H : List V) (v : V) (htwin : IsTwinWheel G H v) (a u b : V)
    (hau : G.Adj a u) (hub : G.Adj u b) (hab : a ≠ b)
    (hN : H.toFinset.filter (fun x => G.Adj v x) = {a, u, b}) :
    ((IsCutset G (closedNbhd G {u} \ {v}) ∧
        ∃ h ∈ H, h ∉ ({a, u, b} : Finset V) ∧ Separates G (closedNbhd G {u} \ {v}) v h) ∨
      (IsCutset G (closedNbhd G {v} \ {u}) ∧
        ∃ h ∈ H, h ∉ ({a, u, b} : Finset V) ∧ Separates G (closedNbhd G {v} \ {u}) u h)) ∧
    (BreaksIn G Finset.univ u (insert v (H.toFinset \ {a, u, b})) ∨
      BreaksIn G Finset.univ v (H.toFinset \ {a, b})) := by sorry

end SubmodPerfect

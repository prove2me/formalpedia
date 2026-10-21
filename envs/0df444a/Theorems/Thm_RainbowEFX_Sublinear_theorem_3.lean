-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_theorem_3
-- name    : RainbowEFX.Sublinear.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:57.075415+00:00
-- url     : https://prove2.me/theorems/b040ac05-a273-4874-9ea0-bb58c377fdb3
-- title:
--   Theorem 3, p. 4 — R(d) ≤ d⁴ + d; a k-partite digraph with k > d⁴ + d parts of size ≤ d and the in-edge property has a cycle visiting each part at most once
-- statement:
--   Let $d\ge 1$. A $k$-partite digraph is a digraph whose vertex set is partitioned into $k$ parts. Say it has the *in-edge property* if for every vertex $w$ and every part $W$ not containing $w$ there is an edge from some vertex of $W$ to $w$. A *rainbow cycle* is a directed cycle that visits each part at most once.
--
--   1. The rainbow cycle number $R(d)$ of Definition 2 is finite, and
--   $$
--   R(d)\le d^4+d .
--   $$
--   2. If $G$ is a $k$-partite digraph with $k>d^4+d$ parts, each of size at most $d$, with the in-edge property, then $G$ contains a rainbow cycle.
--
--   This is the combinatorial core of the paper: through the group champion graph it bounds the number $|L_X|$ of low-demand unallocated goods, which gives the sublinear bound of Theorem 1.
--
--   **Formalization Note** The parts are the fibres of a map `part : V → ι` with `ι` finite; each part is required to have between $1$ and $d$ elements (the paper's "at most $d$" with the nonemptiness that its proof uses; with all parts empty the second claim would be false). Finiteness of $R(d)$ is stated explicitly (`BddAbove`), because `sSup` of an unbounded set of naturals is $0$ in Lean. Cycles have length at least $2$. The claim that the cycle can be found in time polynomial in $k$ is not formalized.
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 4, Theorem 3 (restated as Theorem 21, p. 18)

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem theorem_3 (d : ℕ) (hd : 1 ≤ d) :
    BddAbove {k : ℕ | RainbowFree d k} ∧ rainbowCycleNumber d ≤ d ^ 4 + d ∧
    ∀ {ι V : Type} [Fintype ι] (part : V → ι) (adj : V → V → Prop),
      d ^ 4 + d < Fintype.card ι →
      (∀ i : ι, 1 ≤ Nat.card {w : V // part w = i} ∧ Nat.card {w : V // part w = i} ≤ d) →
      InEdgeProperty part adj →
      ∃ (r : ℕ) (c : Fin r → V), IsRainbowCycle part adj c := by sorry

end RainbowEFX.Sublinear

-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_observation_8
-- name    : TwoOptAllExp.TSP.observation_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:09:59.954312+00:00
-- url     : https://prove2.me/theorems/bbed6bb1-ec3e-441b-9d10-386a74edc994
-- title:
--   Observation 8 — tours contain the edges at degree-two vertices
-- statement:
--   Let $n\ge1$. The vertices of degree two of $G_n$ are exactly $A_i''$, $B_i''$, $C_i''$ for $i\in\{0,\dots,n-1\}$ and $D_i''$ for $i\in[n-1]$, and every tour of $G_n$ contains all edges incident to these vertices.
--
--   These fixed edges are the frame on which the states of a tour are defined.
--
--   Differences from the source:
--   - reading: an instance $I_n$ for each $n\in\mathbb N$ (p. 13, with $0\in\mathbb N$) → $n\ge1$; reason: the construction has distinct layers $F_0$ and $F_n$, and Corollary 14 and the traversals $P_k$ start at $1$
--   - encoding: vertices of $G_n$ with the identified interfaces → the type `Vtx n` of named points, with $X_i$, $X_i''$, $X_i'$ abbreviations of $A_{i-1}'$, $A_{i-1}''$, $A_{i-1}$ and likewise for $Y$; reason: Lean convention; one vertex per identified class, $13n-3$ in total
--   - encoding: a tour as a Hamiltonian cycle → a tour as the edge set of a Hamiltonian cycle (`IsTourOf`); reason: Lean convention; the swaps of p. 7 act on edge sets
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Observation 8, p. 15

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Construction

namespace TwoOptAllExp.TSP

/-- **Observation 8**, p. 15: the degree-two vertices of `G_n` are exactly `A''_i`, `B''_i`, `C''_i`
(`0 ≤ i < n`) and `D''_i` (`i ∈ [n-1]`), and every tour of `G_n` contains the edges incident to
them. -/
theorem observation_8 (n : ℕ) (hn : 1 ≤ n) :
    (∀ v : Vtx n, (G n).degree v = 2 ↔
      v.1.1 = Kind.A2 ∨ v.1.1 = Kind.B2 ∨ v.1.1 = Kind.C2 ∨ v.1.1 = Kind.D2) ∧
    ∀ H : Finset (Sym2 (Vtx n)), IsTourOf (G n) H →
      ∀ u v : Vtx n, (G n).degree v = 2 → (G n).Adj v u → s(v, u) ∈ H := by sorry

end TwoOptAllExp.TSP

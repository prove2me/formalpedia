-- Prove2me | Theorems.Thm_SteinerNav_descent_terminates
-- name    : SteinerNav.descent_terminates
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:39.202669+00:00
-- url     : https://prove2.me/theorems/c02f5324-edc8-4fdf-90c3-d900523dd7a7
-- title:
--   §6.3, p.22 — strict greedy descent terminates on a finite vertex set
-- statement:
--   Let $V\subset\mathbb R^d$ be finite and let $E$ be a directed graph with all edges in $V\times V$. Fix a query $q$ and a start $x_0\in V$. Then
--
--   1. every run of strict greedy descent toward $q$ from $x_0$ has fewer than $|V|$ moves;
--   2. some run from $x_0$ ends at a greedy local minimum.
--
--   The distance to $q$ strictly decreases along a run, so a run never repeats a vertex.
--
--   Differences from the source:
--   - encoding: "Strict descent terminates" → a uniform bound on the length of every run (every tie-breaking), plus existence of a run that stops; reason: termination for every resolution of ties is what "terminates" means when ties are unspecified, and the bound |V| − 1 is the page's reason ("because V is finite").
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), §6.3, p.22

import Mathlib
import Definitions.Def_SteinerNav_GreedyRun

namespace SteinerNav

/-- Strict descent terminates because `V` is finite: on a finite vertex set, every greedy run from
`x₀ ∈ V` toward any query `q` has fewer than `|V|` moves, and a run from `x₀` ending at a local minimum
exists (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §6.3, p.22). -/
theorem descent_terminates {d : ℕ} (V : Finset (Pt d)) (E : Finset (Pt d × Pt d))
    (hE : ∀ x y, (x, y) ∈ E → x ∈ V ∧ y ∈ V) (q x₀ : Pt d) (hx₀ : x₀ ∈ V) :
    (∀ k x, GreedyRun E q x₀ k x → k < V.card) ∧
      ∃ k x, GreedyRun E q x₀ k x ∧ GreedyLocalMin E q x := by sorry

end SteinerNav

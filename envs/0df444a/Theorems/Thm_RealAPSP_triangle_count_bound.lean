-- Prove2me | Theorems.Thm_RealAPSP_triangle_count_bound
-- name    : RealAPSP.triangle_count_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:58:30.025214+00:00
-- url     : https://prove2.me/theorems/be311109-4523-4fdb-a59b-58e83f70dee9
-- title:
--   §5.4 and footnote 9 — at most $O(m^{3/2})$ triangles, hence many popular edges
-- statement:
--   There is an absolute $C_0>0$ such that any graph with $m$ edges has at most $C_0m^{3/2}$ triangles, and likewise any three edge sets on $[n]$ of total size $m$, one in each position of $(i,k)$, $(k,j)$, $(i,j)$, have at most $C_0m^{3/2}$ triples $(i,k,j)$. Consequently, for every $c_1>0$ there is $c_2>0$ such that $c_1n^3/K$ such triples force
--
--   $$m\ge c_2\,\frac{n^2}{K^{2/3}}.$$
--
--   This bounds the number of iterations of the main loop by $O(K^{2/3})$, since each iteration removes the popular edges.
--
--   Differences from the source:
--   - encoding: O(m^{3/2}) and Ω(n²/K^{2/3}) → explicit constants, C₀ absolute and c₂ depending only on c₁; reason: the meaning of the notation
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), §5.4, pp.20–21 (PDF pp.22–23), with footnote 9

import Mathlib
import Definitions.Def_RealAPSP_Triangles

namespace RealAPSP

/-- **§5.4, pp.20–21 (PDF pp.22–23), with footnote 9: the triangle bound.** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…).

Three clauses, with one absolute `C₀`: any simple graph with `m` edges has at most `C₀m^{3/2}` triangles; the same for triples through three edge sets on `[n]`, one in each position, with `m` the total size; and if at least `c₁n³/K` such triples exist, then `m ≥ c₂n²/K^{2/3}`. -/
theorem triangle_count_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        ((G.cliqueFinset 3).card : ℝ) ≤ C₀ * (G.edgeFinset.card : ℝ) ^ ((3 : ℝ) / 2)) ∧
      (∀ (n : ℕ) (EA EB EC : Finset (Fin n × Fin n)),
        (((Finset.univ.filter fun t : Triple n =>
            (t.1, t.2.1) ∈ EA ∧ (t.2.1, t.2.2) ∈ EB ∧ (t.1, t.2.2) ∈ EC).card : ℕ) : ℝ) ≤
          C₀ * ((EA.card + EB.card + EC.card : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) ∧
      ∀ c₁ : ℝ, 0 < c₁ → ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (n : ℕ) (K : ℝ), 1 ≤ K → ∀ EA EB EC : Finset (Fin n × Fin n),
        c₁ * (n : ℝ) ^ 3 / K ≤ (((Finset.univ.filter fun t : Triple n =>
            (t.1, t.2.1) ∈ EA ∧ (t.2.1, t.2.2) ∈ EB ∧ (t.1, t.2.2) ∈ EC).card : ℕ) : ℝ) →
        c₂ * (n : ℝ) ^ 2 / K ^ ((2 : ℝ) / 3) ≤ ((EA.card + EB.card + EC.card : ℕ) : ℝ) := by sorry

end RealAPSP

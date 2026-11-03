-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_matching_polytope_integral_rounding
-- name    : QuantumMaxCutEnergy.matching_polytope_integral_rounding
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-02T21:42:32.575748+00:00
-- url     : https://prove2.me/theorems/c5dc6609-eb2b-49eb-9c72-70b4e2b73c59
-- title:
--   Edmonds exactness: a matching-polytope point is dominated by an integral matching
-- statement:
--   **Edmonds' exactness of the matching polytope, in the form the quantum max-cut matching state needs.**
--
--   Let $G=(V,E)$ be a graph on $n$ vertices, $w\ge0$ a weight on its edges, and $x\ge0$ a nonnegative real weight on
--   the edges satisfying
--
--   * *(vertex loads)* $\sum_{e\ni v} x_e\le 1$ for every vertex $v$, and
--   * *(odd sets)* $\sum_{e\subseteq S} x_e\le \frac{|S|-1}{2}$ for every odd set $S\subseteq V$,
--
--   i.e. $x$ is a point of the fractional matching polytope $P$ of Edmonds.
--
--   **Theorem.** There is a set $M$ of pairwise disjoint edges (an integral matching) with
--   $$\sum_{e\in E} w_e\,x_e\ \le\ \sum_{e\in M} w_e .$$
--   Equivalently, the linear objective $w$ attains over $P$ a value no larger than the maximum weight of an integral
--   matching — Edmonds' exactness of the matching polytope.
--
--   **Why this node exists.** It is the missing half of the matching state in the $0.595$ quantum max-cut analysis
--   (LP24, arXiv:2401.03616, Section 2.3). There, the level-2 Pauli moments give per-edge numbers $h^{+}_e$ that
--   satisfy the star constraint (`QuantumMaxCutEnergy.PauliSDP.moment_positive_excess_star`) and the triangle
--   constraint (`QuantumMaxCutEnergy.PauliSDP.moment_triangle_bound`); by `QuantumMaxCutEnergy.small_odd_sets`
--   (LP24's Lemma 4, proved on the platform, $q=4$) the point $\frac45(2h^{+})=\frac85h^{+}$ lies in $P$. This node then
--   produces an integral maximum-weight matching $M$ with
--   $\sum_{e\in M}w_e\ge\frac85\sum_e w_e h^{+}_e$, which is exactly the $8/5$ factor LP24 use to lower-bound the
--   energy of the matching state. The elementary greedy bound `QuantumMaxCutEnergy.matching_rounding_half` gives only
--   $1/2$ from the vertex loads alone, and no argument using just those loads can do better (the uniform $\frac12$ on
--   a triangle is the standard obstruction); the odd-set constraints are what carry the strength, and extracting an
--   integral matching from them is precisely Edmonds' theorem.
--
--   **Known proof routes.** (i) *Duality/TDI:* write the LP dual of $\max\{w\cdot x : x\in P\}$ (variables on vertices
--   and on odd sets) and prove it has a half-integral optimum, so strong duality yields an integral matching of the
--   same weight; this needs LP duality/Farkas plus the half-integrality of the odd-set system. (ii) *Vertex
--   characterization by uncrossing:* show every vertex of $P$ is an incidence vector of a matching, by uncrossing two
--   crossing tight odd sets (their intersection, union and symmetric difference are again odd, and the
--   corresponding constraints force the support to decompose); a compact objective then attains its maximum at a
--   vertex. (iii) *Blossom / weighted Tutte–Berge:* formalize the weighted blossom algorithm together with the
--   min-max certificate that proves its optimality. Route (ii) is probably the cheapest in a proof assistant: it
--   needs no LP duality, only a finite uncrossing induction on the family of tight odd sets.
-- source:
--   Edmonds, 'Maximum matching and a polyhedron with 0,1-vertices', J. Res. Nat. Bur. Standards 69B (1965); Lee-Parekh arXiv:2401.03616 (ICALP 2024) Section 2.3 (the 8/5 matching weight of the level-2 analysis); Schrijver, Combinatorial Optimization, Ch. 25 (odd-set polytope exactness).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

theorem matching_polytope_integral_rounding {n : ℕ} (w : Weights n) (x : Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0) ≤ 1)
    (hodd : ∀ S : Finset (Fin n), Odd S.card →
      (∑ e ∈ (Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S)), x e) ≤
        ((S.card : ℝ) - 1) / 2) :
    ∃ M : Finset (Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      (∑ e, (w e : ℝ) * x e) ≤ ∑ e ∈ M, (w e : ℝ) := by sorry

end QuantumMaxCutEnergy

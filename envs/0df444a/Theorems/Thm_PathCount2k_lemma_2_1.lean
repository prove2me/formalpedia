-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_1
-- name    : PathCount2k.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:09.977123+00:00
-- url     : https://prove2.me/theorems/032793ef-d8b6-41cf-91fd-a402724df894
-- title:
--   Lemma 2.1 — the wedge of the path vectors is $\Delta_P\cdot e_{[k]}$
-- statement:
--   Let $R$ be a commutative ring, $G=(V,E)$ a directed graph and $g_v\in R^k$ a vector for each vertex. For every directed $k$-vertex path $P=(v_1,\dots,v_k)\in\mathcal P_k$,
--   $$
--   \Phi(P)=g_{v_1}\wedge\cdots\wedge g_{v_k}=\Delta_P\cdot e_{[k]},\qquad \Delta_P=\det[g_{v_1}\cdots g_{v_k}].
--   $$
--
--   The exterior product of the vectors along a path is its determinant times the top basis element; this is what lets the dynamic program sum signed path contributions while walks with a repeated vertex vanish.
--
--   Differences from the source:
--
--   - generalization: the real exterior algebra, 2 ≤ k ≤ n → any commutative ring R, every k; reason: the identity is algebraic; it specializes to R = ℝ and 2 ≤ k ≤ n
--   - generalization: a directed graph (no self-loops discussed) → the arc set may contain self-loops (v, v); reason: a path never uses a loop, so P_k and N are unchanged; on loop-free graphs the statement is the source's
--   - encoding: vertices v ∈ V, positions and coordinates 1, …, k → vertices Fin n, positions and coordinates Fin k (0-based); reason: relabelling; same instances
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.1, p.5

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.1**, p.5: "For every `P ∈ P_k`, `Φ(P) = Δ_P · e_[k]`."

For vertex vectors `g_v ∈ R^k` and a directed `k`-vertex path `P`, the wedge product of the vectors
along `P` is the determinant `Δ_P = det[g_{v₁} ⋯ g_{v_k}]` times the top basis element
`e_[k] = e_{Fin k}`.

**Formalization Note.** Stated over any commutative ring `R` (the paper: `ℝ`) and every `k`
(the paper assumes `2 ≤ k ≤ n`, §2.1). -/
theorem lemma_2_1 {R : Type*} [CommRing R] (n : ℕ) (E : Finset (Fin n × Fin n)) (k : ℕ)
    (g : Fin n → Fin k → R) (P : Fin k → Fin n) (hP : P ∈ paths n E k) :
    Phi g P = Delta g P • (basis Finset.univ : Ext R k) := by sorry

end PathCount2k

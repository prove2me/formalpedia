-- Prove2me | Theorems.Thm_PlanarDFVS_SingleExp_dfvs_weight_bound
-- name    : PlanarDFVS.SingleExp.dfvs_weight_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:50.569012+00:00
-- url     : https://prove2.me/theorems/9bafc835-44e1-418c-85e8-742b44fed9ed
-- title:
--   Lemma 3.3 — weight of a feedback vertex set
-- statement:
--   Let $D$ be a loopless plane digraph with at least one arc; it may be disconnected and may have isolated vertices. Put $w(v)=b(v)-1$ and $L=\sum_vw(v)$. Every directed feedback vertex set $X$ satisfies
--
--   $$|X|+\sum_{v\in X}w(v)\ge L/2+1.$$
--
--   Weights are signed integers and the inequality is evaluated in the reals. No nonnegativity hypothesis is added. The statement includes every nonempty disconnected cyclic core as well as the connected setting used in the source proof. An isolated vertex has weight -1 and contributes zero to the left-hand side, even when selected.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets with corner incidences → Fin n vertices, Fin m arc identities and paired incidence darts; closed walks define cycles; reason: finite relabeling retains loops, parallel arcs and repeated facial incidences; a nonempty closed directed walk contains a directed cycle
--   - encoding: crossing-free plane embedding and its cyclic incidence orders → continuous crossing-free curves with locally straight endpoint germs and ray-ordered rotations; reason: local straightening realizes every finite topological embedding with the same rotations and facial walks; no Euler or target inequality is assumed
--   - generalization: the connected nonempty-arc loopless setting used by Lemma 3.2 in the proof of Lemma 3.3 → all loopless plane digraphs with at least one arc, including disconnected graphs and isolated vertices; reason: specializes to every connected source instance and includes all nonempty disconnected cyclic cores; summing the connected inequalities gives at least one +1 contribution, while isolated vertices contribute -1 to L and zero to the left-hand side
--   - encoding: signed weights and division by two → integer weights are cast into the reals for the displayed inequality; reason: retains exact half-integers without natural truncation
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), p. 6 (PDF p. 6), Lemma 3.3, equation (2)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Interfaces

open scoped BigOperators
open Classical

namespace PlanarDFVS.SingleExp

theorem dfvs_weight_bound (n m : ℕ) (G : Graph n m) (E : Drawing G)
    (hm : 0 < m) (hl : Loopless G)
    (X : Finset (Fin n)) (hX : IsDFVS G X) :
    (X.card : ℝ) + ∑ v ∈ X, (weight E v : ℝ) ≥ (totalWeight E : ℝ) / 2 + 1 := by sorry

end PlanarDFVS.SingleExp

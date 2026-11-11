-- Prove2me | Theorems.Thm_PlanarDFVS_SingleExp_consistent_corners_even
-- name    : PlanarDFVS.SingleExp.consistent_corners_even
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:45.062344+00:00
-- url     : https://prove2.me/theorems/f6c2c3f8-6332-438d-973e-845740ac4c52
-- title:
--   Lemma 3.1 — consistent-corner parity
-- statement:
--   Let $D$ be a weakly connected loopless plane digraph with at least one arc, and let $f$ be any face, including the outer face. Count corner appearances with their sectors and multiplicity along the facial walk. Then
--
--   $$\#\{\text{consistent corners in }f\}\equiv0\pmod2.$$
--
--   This permits the shared face statistic $a(f)$ to be half the consistent-corner count. Parallel arcs and bridges are retained.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets with corner incidences → Fin n vertices, Fin m arc identities and paired incidence darts; closed walks define cycles; reason: finite relabeling retains loops, parallel arcs and repeated facial incidences; a nonempty closed directed walk contains a directed cycle
--   - encoding: crossing-free plane embedding and its cyclic incidence orders → continuous crossing-free curves with locally straight endpoint germs and ray-ordered rotations; reason: local straightening realizes every finite topological embedding with the same rotations and facial walks; no Euler or target inequality is assumed
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), p. 5 (PDF p. 5), Lemma 3.1

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Interfaces

open scoped BigOperators
open Classical

namespace PlanarDFVS.SingleExp

theorem consistent_corners_even (n m : ℕ) (G : Graph n m) (E : Drawing G)
    (hc : WeaklyConnected G) (hm : 0 < m) (hl : Loopless G)
    (f : Finset (Dart m)) (hf : f ∈ faces E) :
    Even (consistentCount E f) := by sorry

end PlanarDFVS.SingleExp

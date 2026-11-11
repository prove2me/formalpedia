-- Prove2me | Theorems.Thm_PlanarDFVS_SingleExp_circular_face_identity
-- name    : PlanarDFVS.SingleExp.circular_face_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:45.718396+00:00
-- url     : https://prove2.me/theorems/3e76da22-ad5a-4624-9917-8bf24e6f6a87
-- title:
--   Lemma 3.2 — exact circular-face identity
-- statement:
--   Let $D$ be a weakly connected loopless plane digraph with at least one arc. Write $2a(f)$ for the consistent corners in face $f$, $2b(v)$ for the alternating corners at vertex $v$, and $\ell_{\rm dir}(D)$ for the number of faces with $a(f)=0$. Then
--
--   $$\ell_{\rm dir}(D)=2+\sum_{f:\,a(f)\ge1}(a(f)-1)+\sum_v(b(v)-1).$$
--
--   Both inner and outer faces and all corner appearances are counted. Subtractions take place in the integers, so source and sink weights may be negative. This exact identity supplies the weight bound.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets with corner incidences → Fin n vertices, Fin m arc identities and paired incidence darts; closed walks define cycles; reason: finite relabeling retains loops, parallel arcs and repeated facial incidences; a nonempty closed directed walk contains a directed cycle
--   - encoding: crossing-free plane embedding and its cyclic incidence orders → continuous crossing-free curves with locally straight endpoint germs and ray-ordered rotations; reason: local straightening realizes every finite topological embedding with the same rotations and facial walks; no Euler or target inequality is assumed
--   - encoding: integer differences a(f)-1 and b(v)-1 → counts are cast into the integers before subtraction; reason: avoids truncated natural subtraction at a zero alternation count
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), p. 6 (PDF p. 6), Lemma 3.2, equation (1)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Interfaces

open scoped BigOperators
open Classical

namespace PlanarDFVS.SingleExp

theorem circular_face_identity (n m : ℕ) (G : Graph n m) (E : Drawing G)
    (hc : WeaklyConnected G) (hm : 0 < m) (hl : Loopless G) :
    ((circularFaces E).card : ℤ) = 2 +
      ∑ f ∈ (faces E).filter (fun f => 1 ≤ a E f), ((a E f : ℤ) - 1) +
      ∑ v, ((b E v : ℤ) - 1) := by sorry

end PlanarDFVS.SingleExp

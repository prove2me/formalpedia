-- Prove2me | Theorems.Thm_PolyhedralPacking1261_Packing_Supplement_lemma_15
-- name    : PolyhedralPacking1261.Packing.Supplement.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:39:49.37919+00:00
-- url     : https://prove2.me/theorems/a10e9679-069a-4757-877d-8565f0716591
-- title:
--   Lemma 15 — polynomial-time repacking into $[0,1]^2\times[0,64V/s^2+16h]$
-- statement:
--   Let $0<s\le1$ and $h>0$. Suppose objects whose x- and y-widths are at most $1-s$ and whose z-widths are at most $h$ are packed by translations into finitely many axis-parallel boxes of total volume $V$. Then in polynomial time they can be repacked by translations into the box
--
--   $$[0,1]\times[0,1]\times\Big[0,\ \frac{64V}{s^2}+16h\Big].$$
--
--   Precisely: there is one polynomial-time algorithm that reads the finite metadata only — $s$, $h$, the host boxes, and for each object its host box, a bounding box (x- and y-widths at most $1-s$, z-width at most $h$, translated into its host box) and its translation — and outputs a new translation for each object. For every family of sets contained in the given bounding boxes whose translates have disjoint interiors within each host box, the new translates lie in the box above and have pairwise disjoint interiors.
--
--   This is the combining step of the paper's main algorithm and the core of its reduction to bin and strip packing (Theorem 3).
--
--   **Formalization Note** The algorithm is a finite program of the base mission's scalar machine with $s,h$ part of its input; interiors are ambient.
--
--   Differences from the source:
--   - generalization: fixed 0 < s ≤ 1 and h > 0; in polynomial time → one program and one polynomial bound for all s, h, which are read from the input; reason: a uniform algorithm specializes to every fixed (s, h); the paper itself calls the lemma with input-dependent h = w_z
--   - generalization: objects whose widths are at most 1 − s, 1 − s, h, packed into the boxes → objects contained in supplied bounding boxes with those widths whose translates lie in the host boxes; disjoint interiors required only within a common host box; reason: the tight bounding box of an object in its host box qualifies, and boxes packed apart from each other satisfy the weaker disjointness, so the source's situation is a special case
--   - reading: In polynomial time, they can be repacked by translations into the box → a terminating execution with time ≤ coefficient·(input length + 1)^degree, and every execution's output translations repack every consistent family into [0,1]²×[0,64V/s²+16h] with pairwise disjoint interiors; reason: the algorithmic and geometric content of the sentence, in the base mission's computational model
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, Lemma 15 and its proof, §4.2, PDF pp.19–20 (printed pp.18–19)

import Definitions.Def_PolyhedralPacking1261_Packing_Supplement_Containers

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing.Supplement

open PolyhedralPacking1261.Packing

/-- Lemma 15, PDF p.19 (printed p.18). One finite scalar program, reading only the box
metadata (`s`, `h`, host boxes, bounding boxes, host assignment, translations), runs in
polynomial time and outputs new translations that repack every family of objects
consistent with the metadata into `[0,1] × [0,1] × [0, 64V/s² + 16h]`, where `V` is the
total volume of the host boxes. Objects in a common host box are assumed to have
disjoint interiors; the output has pairwise disjoint interiors. -/
theorem lemma_15 :
    ∃ program : ScalarProgram, ∃ coefficient degree : ℕ, 0 < coefficient ∧
      ∀ I : RepackInstance, I.Valid →
        (∃ time out, RepackExecution program I time out ∧
          time ≤ coefficient * ((repackWords I).length + 1) ^ degree) ∧
        ∀ time out, RepackExecution program I time out →
          ∀ S : Fin I.objectCount → Set Point3,
            (∀ i, S i ⊆ closedBox (I.bboxLower i) (I.bboxUpper i)) →
            (∀ i j, i ≠ j → I.host i = I.host j →
              Disjoint (interior (shiftSet (I.translation i) (S i)))
                (interior (shiftSet (I.translation j) (S j)))) →
            (∀ i, shiftSet (out i) (S i) ⊆
              stripContainer (64 * I.totalVolume / I.s ^ 2 + 16 * I.h)) ∧
            ∀ i j, i ≠ j →
              Disjoint (interior (shiftSet (out i) (S i)))
                (interior (shiftSet (out j) (S j))) := by sorry

end PolyhedralPacking1261.Packing.Supplement

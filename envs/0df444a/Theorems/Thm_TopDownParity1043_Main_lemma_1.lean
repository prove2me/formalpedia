-- Prove2me | Theorems.Thm_TopDownParity1043_Main_lemma_1
-- name    : TopDownParity1043.Main.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:19:46.412878+00:00
-- url     : https://prove2.me/theorems/9c8e1c93-74fa-47dc-a296-5dc9259c0223
-- title:
--   Lemma 1 ([KW90]) — circuits and bounded-round KW protocols
-- statement:
--   For all natural numbers $n,d,m$ and every Boolean function $f:\{0,1\}^n\to\{0,1\}$,
--   $$\begin{aligned}&\exists C\text{ computing }f:\quad\operatorname{depth}(C)\le d,\quad\operatorname{maxFanIn}(C)\le2^m\\&\qquad\Longleftrightarrow\quad\mathrm{KW}(f)\text{ has an at-most-}d\text{-round protocol of cost at most }m.\end{aligned}$$
--
--   Alice holds a zero-input and Bob a one-input. Each actual input pair must produce a coordinate of disagreement, while the next speaker can depend arbitrarily on the previous messages. Both directions apply also to constant functions and to $n=0$; a no-output leaf is correct only on an empty reached rectangle. This correspondence connects the communication and circuit clauses of the goal.
--
--   Differences from the source:
--   - encoding: at most d messages of at most m bits, with a coordinate output → finite trees with at most 2^m children per node, height at most d and optional outputs; reason: the node fixes the transcript and speaker; every actual input pair must output a differing coordinate, and missing outputs only represent empty reached rectangles
--   - generalization: De Morgan circuits without an explicit constant and empty-gate convention → the referenced AND/OR DAGs also allow constants, empty gates and literal or constant outputs; reason: this includes every source circuit with the same depth and wire count; constants and empty gates can be simplified without increasing either resource
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), Lemma 1 ([KW90]), p. 2

import Mathlib
import Definitions.Def_TopDownParity1043_Main_KW

set_option autoImplicit false
open scoped NNReal ENNReal

namespace TopDownParity1043.Main

/-- Lemma 1 ([KW90]), p.2, the full equivalence. Constants and empty gates
are retained from the reused circuit definition. No-output leaves are allowed only
on empty reached rectangles. In particular n=d=m=0 and constant functions are covered. -/
theorem lemma_1 (n d m : ℕ) (f : ParityBarrier563.Trilinear.BoolFn (Fin n)) :
    (∃ C : ParityBarrier563.Trilinear.Circuit (Fin n),
      C.depth ≤ d ∧ maxFanIn C ≤ 2 ^ m ∧ C.Computes f) ↔
    HasKWProtocol f d m := by sorry

end TopDownParity1043.Main

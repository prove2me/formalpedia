-- Prove2me | Theorems.Thm_Turing_TM2ComputableInPolyTime_iterate_length
-- name    : Turing.TM2ComputableInPolyTime.iterate_length
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:39:31.106819+00:00
-- url     : https://prove2.me/theorems/c1eff597-cee3-4554-a4b3-32c89fb793a5
-- title:
--   Iterating a length-nonincreasing polynomial-time map $|x|$ times
-- statement:
--   Let $g:\{0,1\}^*\to\{0,1\}^*$ be computable in polynomial time by a finite multi-stack Turing machine (Mathlib's `TM2ComputableInPolyTime`, bit strings encoded by themselves), and suppose $g$ never increases length: $|g(x)|\le|x|$ for all $x$. Then the map
--
--   $$x\ \longmapsto\ g^{|x|}(x)\qquad(\text{$g$ iterated $|x|$ times})$$
--
--   is also computable in polynomial time.
--
--   This closure property lets a polynomial-time algorithm repeat a black-box polynomial-time round as many times as its input length, as in the repeated-bypass algorithm for cut-covering sets (Theorem 1.2), where each round removes one vertex and so shrinks the encoded graph.
--
--   **Formalization Note** The time bound is $T(|x|)\cdot|x|$ plus linear overhead, using that every intermediate string has length at most $|x|$.
-- source:
--   Standard closure property of polynomial time; stated for Mathlib's TM2ComputableInPolyTime (Mathlib/Computability/TuringMachine/Computable.lean). Needed for the repeated bypass rounds in Koana–Kumabe, A Deterministic Polynomial Kernel for Odd Cycle Transversal, proof of Theorem 1.2, p. 14.

import Mathlib

theorem Turing.TM2ComputableInPolyTime.iterate_length {g : List Bool → List Bool}
    (h : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (hlen : ∀ x, (g x).length ≤ x.length) :
    Nonempty (Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => g^[x.length] x)) := by sorry

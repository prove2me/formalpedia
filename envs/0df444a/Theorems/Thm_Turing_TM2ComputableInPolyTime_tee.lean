-- Prove2me | Theorems.Thm_Turing_TM2ComputableInPolyTime_tee
-- name    : Turing.TM2ComputableInPolyTime.tee
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:24:02.273963+00:00
-- url     : https://prove2.me/theorems/2b08ccac-6b90-57ce-9509-ffd979f07aac
-- title:
--   Polynomial-time machines can keep their input (tee combinator)
-- statement:
--   Let $\alpha,\beta$ be types with binary encodings $e_\alpha:\alpha\to\{0,1\}^*$ and $e_\beta:\beta\to\{0,1\}^*$, and let $f:\alpha\to\beta$ be computable in polynomial time by a finite multi-stack Turing machine (Mathlib's `TM2ComputableInPolyTime`). Then the map that keeps its input and appends the output,
--
--   $$e_\alpha(a)\;\longmapsto\;e_\alpha(a)\,\Vert\,e_\beta(f(a)),$$
--
--   is also computable in polynomial time. Formally, the identity function $\alpha\to\alpha$ is polynomial-time computable from the encoding $e_\alpha$ to the encoding $a\mapsto e_\alpha(a)\Vert e_\beta(f(a))$, where $\Vert$ denotes concatenation of bit strings.
--
--   This is the standard "keep the input" (tee) closure property of polynomial time. Together with closure under composition it lets a polynomial-time algorithm call a black-box polynomial-time subroutine and still consult its original input afterwards, as in the compression step of Lemma 5.1 (run the cut-covering algorithm of Theorem 1.2 on a derived digraph, then post-process using the original graph and transversal).
--
--   **Formalization Note** Both encodings are over `Bool`; the machine's alphabets are related to `Bool` by the equivalences carried in `TM2ComputableAux`.
-- source:
--   Standard closure property of polynomial time (e.g. Arora–Barak, Computational Complexity: A Modern Approach, §1.6 / Claim 1.6-style composition of TMs); stated for Mathlib's TM2ComputableInPolyTime (Mathlib/Computability/TuringMachine/Computable.lean). Needed for Koana–Kumabe, A Deterministic Polynomial Kernel for Odd Cycle Transversal, Lemma 5.1, p. 15.

import Mathlib

theorem Turing.TM2ComputableInPolyTime.tee {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β} (h : Turing.TM2ComputableInPolyTime ea eb f) :
    Nonempty (Turing.TM2ComputableInPolyTime ea (fun a => ea a ++ eb (f a)) id) := by sorry

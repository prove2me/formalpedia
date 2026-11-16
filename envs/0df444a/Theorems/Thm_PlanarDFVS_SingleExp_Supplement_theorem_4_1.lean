-- Prove2me | Theorems.Thm_PlanarDFVS_SingleExp_Supplement_theorem_4_1
-- name    : PlanarDFVS.SingleExp.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:33:51.65555+00:00
-- url     : https://prove2.me/theorems/5f4d245d-783c-4341-90de-18965902145c
-- title:
--   Theorem 4.1 — randomized polynomial-space algorithm at base 6.75
-- statement:
--   Let $D$ be any planar directed multigraph with $n$ vertices and let $k\in\mathbb N$. Loops, parallel and antiparallel arcs and disconnected graphs are allowed; no embedding or optimum is supplied. Set $N=\max(1,n)$ and let $\ell$ be the encoded input length.
--
--   There is one fixed binary program using fair random bits, with absolute constants $C,S>0$ and fixed degrees $d,e\in\mathbb N$, such that on every input it halts on every random execution, always returns either a directed feedback vertex set of size at most $k$ or Fail, and satisfies
--
--   $$T\le C\cdot 6.75^{k}N^{d},\qquad\text{space}\le S\,\ell^{e},\qquad \Pr[\text{solution}]\ge\tfrac12\ \text{ whenever a solution exists}.$$
--
--   This is the paper's first, simpler randomized algorithm; the published Theorem 4.2 improves the base to $2+\sqrt5$.
--
--   Differences from the source:
--   - reading: randomized algorithm, O(6.75^k n^{O(1)}) time and polynomial space with the machine model unspecified → one finite binary fair-bit instruction program with charged bit operations, fixed C, S > 0 and d, e before every input; reason: the published RandomGuarantee interface used by Theorem 4.2; no sampling oracle or cost certificate
--   - reading: the input digraph with arbitrarily many duplicate arcs → n, binary k and the n by n directed support bits, including loops; reason: every multigraph has the same cycles and DFVS answers as its support; same convention as the published Theorem 4.2
--   - encoding: bounded randomized running time and polynomial space → a common halting horizon per input, every bit prefix within the time bound, maximum live workspace along every execution; reason: same convention as the published Theorem 4.2
--   - encoding: O(6.75^k n^{O(1)}) → C · (675/100)^k · max(1,n)^d; reason: base exactly 6.75; max(1,n) avoids a vanishing bound at n = 0
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), p. 9 (PDF p. 9), Theorem 4.1

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Interfaces

open scoped BigOperators
open Classical

namespace PlanarDFVS.SingleExp.Supplement

open PlanarDFVS.SingleExp

theorem theorem_4_1 :
    ∃ (R : Program) (C S : ℝ) (d e : ℕ), 0 < C ∧ 0 < S ∧
      RandomGuarantee R (675 / 100) C d S e := by sorry

end PlanarDFVS.SingleExp.Supplement

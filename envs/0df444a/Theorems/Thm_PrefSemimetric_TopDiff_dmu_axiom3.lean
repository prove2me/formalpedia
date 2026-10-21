-- Prove2me | Theorems.Thm_PrefSemimetric_TopDiff_dmu_axiom3
-- name    : PrefSemimetric.TopDiff.dmu_axiom3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:33.368611+00:00
-- url     : https://prove2.me/theorems/bef13bb9-4204-4d78-bea9-3da090b2815f
-- title:
--   §3.3, pp. 16–17 — every D^µ satisfies Axiom 3
-- statement:
--   Let $X$ be a finite set and $\mu$ a positive measure on $2^X$. For every acyclic order $\succsim$ and distinct $a,b\in X$:
--
--   1. if $a$ and $b$ are not $\succ$-comparable and $\succsim\oplus(a,b)$ is an acyclic order, then
--   $$D^\mu(\succsim,\succsim\oplus(a,b))=2^{N(b,\succsim)-1}\,D^\mu(\succsim_{ab},\succsim^+_{ab});$$
--   2. if $a\succ b$, then
--   $$D^\mu(\succsim,\succsim\ominus(a,b))=2^{N(b,\succsim)}\,D^\mu(\succsim_{ab},\succsim^+_{ab}).$$
--
--   Here $N(b,\succsim)$ is the number of alternatives other than $b$ that are not strictly above $b$. This is the counting half of the "if" direction of Theorem 3.1.
--
--   **Formalization Note** The statement is `Axiom3 (Dmu w)` with $w\ge0$. In clause 1, $N(b,\succsim)\ge1$ because $a$ is counted, so the natural-number exponent $N-1$ is exact.
-- source:
--   Nishimura & Ok, A Class of Dissimilarity Semimetrics for Preference Relations, arXiv:2203.04418v1, pp. 16–17, §3.3, proof of Theorem 3.1, display (9) and the sentence 'That Dµ(≿, ≿⊖(a, b)) = 2N(b,≿)Dµ(≿ab, ≿+ab) when a ≻ b is analogously proved.'; Axiom 3, p. 15

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

namespace PrefSemimetric.TopDiff

theorem dmu_axiom3 {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    Axiom3 (Dmu w) := by sorry

end PrefSemimetric.TopDiff

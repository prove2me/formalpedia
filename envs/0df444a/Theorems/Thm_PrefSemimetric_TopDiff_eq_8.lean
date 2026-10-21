-- Prove2me | Theorems.Thm_PrefSemimetric_TopDiff_eq_8
-- name    : PrefSemimetric.TopDiff.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:33.114986+00:00
-- url     : https://prove2.me/theorems/ef9c9798-a040-4641-81a6-4897a488897b
-- title:
--   Display (8), p. 16 — D^µ(≿_ab, ≿⁺_ab) = µ{b}
-- statement:
--   Let $X$ be a finite set, $\mu$ a positive measure on $2^X$, and $a,b\in X$ distinct. The relations $\succsim_{ab}$ (every alternative other than $a,b$ strictly above both $a$ and $b$, nothing else) and $\succsim^+_{ab}$ (the same, plus $a$ strictly above $b$) are acyclic orders, and
--   $$D^\mu(\succsim_{ab},\succsim^+_{ab})=\mu\{b\}.$$
--
--   The value shows that $d(\succsim_{ab},\succsim^+_{ab})$ plays the role of the point mass $\mu\{b\}$ in Axiom 3, which is how the measure is recovered in the "only if" direction of Theorem 3.1.
--
--   **Formalization Note** $\mu\{b\}=w(b)$ for the point weights $w\ge0$. The two acyclicity conjuncts record that both relations lie in $\mathcal A(X)$, as the page's "partial orders" asserts.
-- source:
--   Nishimura & Ok, A Class of Dissimilarity Semimetrics for Preference Relations, arXiv:2203.04418v1, p. 16, display (8); ≿ab, ≿+ab defined p. 14

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

namespace PrefSemimetric.TopDiff

theorem eq_8 {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (a b : X) (hab : a ≠ b) :
    IsAcyclicOrder (prefAB a b) ∧ IsAcyclicOrder (prefABplus a b) ∧
      Dmu w (prefAB a b) (prefABplus a b) = w b := by sorry

end PrefSemimetric.TopDiff

-- Prove2me | Theorems.Thm_PrefSemimetric_TopDiff_lemma_3_4
-- name    : PrefSemimetric.TopDiff.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:40.200285+00:00
-- url     : https://prove2.me/theorems/0ece2417-06d0-4e29-8c67-db7399235af9
-- title:
--   Lemma 3.4, p. 17 — under Axioms 1 and 3, d(≿_ab, ≿⁺_ab) does not depend on a
-- statement:
--   Let $X$ be a finite set and let $d$ be a semimetric on the acyclic orders $\mathcal A(X)$, with values in $[0,\infty)$, that satisfies Axioms 1 and 3. Then
--   $$d(\succsim_{ab},\succsim^+_{ab})=d(\succsim_{cb},\succsim^+_{cb})$$
--   for all distinct $a,b,c\in X$.
--
--   Hence $m_b:=d(\succsim_{ab},\succsim^+_{ab})$ depends only on $b$; these numbers are the point masses of the measure $\mu$ constructed in the "only if" direction of Theorem 3.1.
--
--   **Formalization Note** "Semimetric" is the pseudometric reading `IsSemimetric` on relations satisfying `IsAcyclicOrder`.
-- source:
--   Nishimura & Ok, A Class of Dissimilarity Semimetrics for Preference Relations, arXiv:2203.04418v1, p. 17, Lemma 3.4

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

namespace PrefSemimetric.TopDiff

theorem lemma_3_4 {X : Type*} [Fintype X] [DecidableEq X]
    (d : (X → X → Prop) → (X → X → Prop) → ℝ) (hd : IsSemimetric d)
    (h1 : Axiom1 d) (h3 : Axiom3 d) (a b c : X) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    d (prefAB a b) (prefABplus a b) = d (prefAB c b) (prefABplus c b) := by sorry

end PrefSemimetric.TopDiff

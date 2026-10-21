-- Prove2me | Theorems.Thm_PrefSemimetric_TopDiff_agree_same_symmPart
-- name    : PrefSemimetric.TopDiff.agree_same_symmPart
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:45.316326+00:00
-- url     : https://prove2.me/theorems/5ad53cd8-1f4f-4735-a271-94a88ebd28d4
-- title:
--   §3.3, proof of Theorem 3.1, pp. 17–18 — d = D^µ on acyclic orders with equal symmetric parts
-- statement:
--   Let $X$ be a finite set and let $d$ be a semimetric on $\mathcal A(X)$ satisfying Axioms 1 and 3. Let $\mu$ be the measure on $2^X$ with point masses $\mu\{b\}=d(\succsim_{ab},\succsim^+_{ab})$ for every $a\ne b$. Then for all acyclic orders $\succsim,\trianglerighteq$ with the same symmetric parts,
--   $$d(\succsim,\trianglerighteq)=D^\mu(\succsim,\trianglerighteq).$$
--
--   Together with Axiom 4, which lets one replace each order by its strict part plus the diagonal, this yields the "only if" direction of Theorem 3.1.
--
--   **Formalization Note** As in the previous milestone, $\mu$ is given by point weights `w` with $w(b)=d(\succsim_{ab},\succsim^+_{ab})$ for all $a\ne b$. The case $\succsim=\trianglerighteq$ is included (both sides are $0$).
-- source:
--   Nishimura & Ok, A Class of Dissimilarity Semimetrics for Preference Relations, arXiv:2203.04418v1, pp. 17–18, §3.3, proof of Theorem 3.1 ('Now take any ≿, ⊵ ∈ A(X) and assume that the symmetric parts of these relations are the same.' … 'where the third equality follows from the fact that Dµ satisfies Axiom 1’.')

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

namespace PrefSemimetric.TopDiff

theorem agree_same_symmPart {X : Type*} [Fintype X] [DecidableEq X]
    (d : (X → X → Prop) → (X → X → Prop) → ℝ) (hd : IsSemimetric d)
    (h1 : Axiom1 d) (h3 : Axiom3 d)
    (w : X → ℝ) (hw : ∀ a b, a ≠ b → w b = d (prefAB a b) (prefABplus a b))
    (R T : X → X → Prop) (hR : IsAcyclicOrder R) (hT : IsAcyclicOrder T)
    (hsymm : ∀ x y, symmPart R x y ↔ symmPart T x y) :
    d R T = Dmu w R T := by sorry

end PrefSemimetric.TopDiff

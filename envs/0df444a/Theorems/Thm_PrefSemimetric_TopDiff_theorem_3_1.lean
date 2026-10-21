-- Prove2me | Theorems.Thm_PrefSemimetric_TopDiff_theorem_3_1
-- name    : PrefSemimetric.TopDiff.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:43.440084+00:00
-- url     : https://prove2.me/theorems/d3c1dd3e-eaf0-4caa-b145-7ee5d862bb9f
-- title:
--   Theorem 3.1, p. 15 — a semimetric on acyclic orders satisfies Axioms 1, 3, 4 iff it is a µ-top-difference semimetric
-- statement:
--   Let $X$ be a nonempty finite set and let $d$ be a semimetric on the set $\mathcal A(X)$ of acyclic orders on $X$, with values in $[0,\infty)$. Then $d$ satisfies Axioms 1, 3 and 4 if and only if there is a positive measure $\mu$ on $2^X$ such that
--   $$d(\succsim,\trianglerighteq)=D^\mu(\succsim,\trianglerighteq)=\sum_{S\subseteq X}\mu\big(M(S,\succsim)\triangle M(S,\trianglerighteq)\big)\qquad\text{for all }\succsim,\trianglerighteq\in\mathcal A(X).$$
--
--   The axioms are: (1) additivity along orders in-between two given orders, where "in-between" means reachable by one-step perturbations obeying the consistency condition (2) of p. 10; (3) the distance of a single addition or deletion of $(a,b)$ is $2^{N(b,\succsim)-1}$, resp. $2^{N(b,\succsim)}$, times $d(\succsim_{ab},\succsim^+_{ab})$; (4) orders with the same strict part are at distance $0$. The theorem identifies the $\mu$-top-difference semimetrics, which compare two preferences by the maximal elements they select from every menu, as exactly the semimetrics with these three properties.
--
--   **Formalization Note** Relations are `X → X → Prop` and $d$ is a real function on all of them; `IsSemimetric d` (nonnegativity, $d(R,R)=0$, symmetry, triangle inequality on acyclic orders) is the pseudometric reading of "semimetric", and the conclusion asserts equality only on acyclic orders. One measure $\mu$, given by point weights $w\ge0$ with $\mu(T)=\sum_{x\in T}w(x)$, serves all pairs (the zero measure is allowed, as in footnote 14). Axiom 3's $\oplus$ clause applies only when $\succsim\oplus(a,b)$ is acyclic, as on p. 8. Axiom 1 uses the paper's "in-between", not the literature's weaker betweenness.
-- source:
--   Nishimura & Ok, A Class of Dissimilarity Semimetrics for Preference Relations, arXiv:2203.04418v1, p. 15, Theorem 3.1

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

namespace PrefSemimetric.TopDiff

theorem theorem_3_1 {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (d : (X → X → Prop) → (X → X → Prop) → ℝ) (hd : IsSemimetric d) :
    (Axiom1 d ∧ Axiom3 d ∧ Axiom4 d) ↔
      ∃ w : X → ℝ, (∀ x, 0 ≤ w x) ∧
        ∀ R T, IsAcyclicOrder R → IsAcyclicOrder T → d R T = Dmu w R T := by sorry

end PrefSemimetric.TopDiff

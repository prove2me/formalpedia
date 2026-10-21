-- Prove2me | Theorems.Thm_PrefSemimetric_TopDiff_dmu_isSemimetric
-- name    : PrefSemimetric.TopDiff.dmu_isSemimetric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:25.462026+00:00
-- url     : https://prove2.me/theorems/2d806200-01a2-4fe5-b953-e66da3274ad6
-- title:
--   §3.1, p. 12 — each µ-top-difference D^µ is a semimetric on acyclic orders
-- statement:
--   Let $X$ be a nonempty finite set and $\mu$ a positive measure on $2^X$. Then the $\mu$-top-difference function
--   $$D^\mu(\succsim,\trianglerighteq)=\sum_{S\subseteq X}\mu\big(M(S,\succsim)\triangle M(S,\trianglerighteq)\big)$$
--   is a semimetric on the set $\mathcal A(X)$ of acyclic orders on $X$: for all acyclic orders $\succsim,\trianglerighteq,\unrhd'$,
--
--   1. $D^\mu(\succsim,\trianglerighteq)\ge 0$;
--   2. $D^\mu(\succsim,\succsim)=0$;
--   3. $D^\mu(\succsim,\trianglerighteq)=D^\mu(\trianglerighteq,\succsim)$;
--   4. $D^\mu(\succsim,\unrhd')\le D^\mu(\succsim,\trianglerighteq)+D^\mu(\trianglerighteq,\unrhd')$.
--
--   This makes $D^\mu$ an admissible candidate in Theorem 3.1, which characterizes exactly these semimetrics.
--
--   **Formalization Note** $\mu$ is given by point weights $w\ge0$, $\mu(T)=\sum_{x\in T}w(x)$. "Semimetric" is read as a pseudometric with values in $[0,\infty)$ (the conjuncts above), on relations satisfying `IsAcyclicOrder`.
-- source:
--   Nishimura & Ok, A Class of Dissimilarity Semimetrics for Preference Relations, arXiv:2203.04418v1, p. 12, §3.1 ('That each Dµ is indeed a semimetric on A(X) is straightforward.')

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

namespace PrefSemimetric.TopDiff

theorem dmu_isSemimetric {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    IsSemimetric (Dmu w) := by sorry

end PrefSemimetric.TopDiff

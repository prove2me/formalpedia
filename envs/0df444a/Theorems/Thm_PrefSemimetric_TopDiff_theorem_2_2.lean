-- Prove2me | Theorems.Thm_PrefSemimetric_TopDiff_theorem_2_2
-- name    : PrefSemimetric.TopDiff.theorem_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:38.300078+00:00
-- url     : https://prove2.me/theorems/5f628e9b-8353-46ef-9cec-d7e6d1bfdc94
-- title:
--   Theorem 2.2, p. 11 — acyclic orders with equal symmetric parts are joined by finitely many one-step perturbations
-- statement:
--   Let $X$ be a finite set and let $\succsim$ and $\trianglerighteq$ be distinct acyclic orders on $X$ with the same symmetric parts, i.e. $x\sim y$ under $\succsim$ iff $x$ and $y$ are mutually related by $\trianglerighteq$. Then $\succsim$ can be transformed into $\trianglerighteq$ by finitely many one-step perturbations: there are acyclic orders $\succsim_0,\dots,\succsim_{n-1}$ with $\succsim_{n-1}=\trianglerighteq$ and
--   $$\succsim\to\succsim_0\twoheadrightarrow\trianglerighteq,\qquad \succsim_{k-1}\to\succsim_k\twoheadrightarrow\trianglerighteq\quad(k=1,\dots,n-1).$$
--   Equivalently, $\trianglerighteq$ is in-between $\succsim$ and $\trianglerighteq$.
--
--   This is the reachability result on which the "only if" half of Theorem 3.1 rests: it lets distances between orders with a common symmetric part be computed along a chain of single additions and deletions.
--
--   **Formalization Note** The conclusion is `InBetween R T T`, the transitive closure of the one-step relation toward $T$, which is the page's "$n$-step perturbation of $\succsim$ toward $\trianglerighteq$ for some $n\ge1$" with $\succsim^*=\trianglerighteq$. Each one-step perturbation carries its consistency condition (2).
-- source:
--   Nishimura & Ok, A Class of Dissimilarity Semimetrics for Preference Relations, arXiv:2203.04418v1, p. 11, Theorem 2.2 (definitions of one-step and n-step perturbation, pp. 9–10)

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

namespace PrefSemimetric.TopDiff

theorem theorem_2_2 {X : Type*} [Fintype X] [DecidableEq X]
    (R T : X → X → Prop) (hR : IsAcyclicOrder R) (hT : IsAcyclicOrder T) (hne : R ≠ T)
    (hsymm : ∀ x y, symmPart R x y ↔ symmPart T x y) :
    InBetween R T T := by sorry

end PrefSemimetric.TopDiff

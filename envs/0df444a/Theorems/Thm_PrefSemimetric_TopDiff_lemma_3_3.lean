-- Prove2me | Theorems.Thm_PrefSemimetric_TopDiff_lemma_3_3
-- name    : PrefSemimetric.TopDiff.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:34.43301+00:00
-- url     : https://prove2.me/theorems/3815e5e1-956c-4bf9-a969-508d32eda8c4
-- title:
--   Lemma 3.3, p. 16 — along ≿ → ≿₀ ↠ ⊵ the menu-wise symmetric differences split disjointly
-- statement:
--   Let $X$ be a finite set and let $\succsim,\succsim_0,\trianglerighteq$ be acyclic orders on $X$ with $\succsim\to\succsim_0\twoheadrightarrow\trianglerighteq$ (that is, $\succsim_0$ is a one-step perturbation of $\succsim$ toward $\trianglerighteq$). Then for every $S\subseteq X$ the sets
--   $$M(S,\succsim)\triangle M(S,\succsim_0)\quad\text{and}\quad M(S,\succsim_0)\triangle M(S,\trianglerighteq)$$
--   are disjoint, and their union equals $M(S,\succsim)\triangle M(S,\trianglerighteq)$.
--
--   The lemma says that a one-step perturbation toward $\trianglerighteq$ never moves the set of maximal elements of a menu away from that of $\trianglerighteq$; summed over menus it gives the additivity (Axiom 1′) of every $D^\mu$.
--
--   **Formalization Note** $M(S,\cdot)$ is `maxSet S`, with `S` ranging over all finite subsets of $X$.
-- source:
--   Nishimura & Ok, A Class of Dissimilarity Semimetrics for Preference Relations, arXiv:2203.04418v1, p. 16, Lemma 3.3

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

namespace PrefSemimetric.TopDiff

theorem lemma_3_3 {X : Type*} [Fintype X] [DecidableEq X]
    (R R0 T : X → X → Prop) (hR : IsAcyclicOrder R) (hT : IsAcyclicOrder T)
    (h : OneStepToward R R0 T) (S : Finset X) :
    Disjoint (symmDiff (maxSet S R) (maxSet S R0)) (symmDiff (maxSet S R0) (maxSet S T)) ∧
      symmDiff (maxSet S R) (maxSet S R0) ∪ symmDiff (maxSet S R0) (maxSet S T) =
        symmDiff (maxSet S R) (maxSet S T) := by sorry

end PrefSemimetric.TopDiff

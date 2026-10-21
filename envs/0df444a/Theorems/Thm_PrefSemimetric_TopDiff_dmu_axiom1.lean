-- Prove2me | Theorems.Thm_PrefSemimetric_TopDiff_dmu_axiom1
-- name    : PrefSemimetric.TopDiff.dmu_axiom1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:39.627117+00:00
-- url     : https://prove2.me/theorems/4804fb49-9fb5-4f04-b16b-6551b1123777
-- title:
--   §3.3, p. 16 — every D^µ satisfies Axiom 1′ and Axiom 1
-- statement:
--   Let $X$ be a finite set and $\mu$ a positive measure on $2^X$. Then $D^\mu$ satisfies
--
--   1. **Axiom 1′**: for all acyclic orders $\succsim,\succsim_0,\trianglerighteq$ with $\succsim\to\succsim_0\twoheadrightarrow\trianglerighteq$,
--   $$D^\mu(\succsim,\trianglerighteq)=D^\mu(\succsim,\succsim_0)+D^\mu(\succsim_0,\trianglerighteq);$$
--   2. **Axiom 1**: the same identity whenever $\succsim_0$ is in-between $\succsim$ and $\trianglerighteq$.
--
--   This is the additivity half of the "if" direction of Theorem 3.1.
--
--   **Formalization Note** $\mu$ is given by point weights $w\ge0$. Acyclicity of $\succsim_0$ is part of the one-step relation.
-- source:
--   Nishimura & Ok, A Class of Dissimilarity Semimetrics for Preference Relations, arXiv:2203.04418v1, p. 16, §3.3, proof of Theorem 3.1 ('An obvious application of Lemma 3.3 shows that Dµ satisfies Axiom 1’, and by induction, Axiom 1.'); Axioms 1 and 1′, p. 13

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

namespace PrefSemimetric.TopDiff

theorem dmu_axiom1 {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∀ R R0 T, IsAcyclicOrder R → IsAcyclicOrder T → OneStepToward R R0 T →
        Dmu w R T = Dmu w R R0 + Dmu w R0 T) ∧
      Axiom1 (Dmu w) := by sorry

end PrefSemimetric.TopDiff

-- Prove2me | Theorems.Thm_PrefSemimetric_TopDiff_agree_single_perturbation
-- name    : PrefSemimetric.TopDiff.agree_single_perturbation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:36.239554+00:00
-- url     : https://prove2.me/theorems/344b6d56-8c3f-4962-a2c6-6af587efc388
-- title:
--   §3.3, proof of Theorem 3.1, p. 17 — d = D^µ on single additions and deletions
-- statement:
--   Let $X$ be a finite set and let $d$ be a semimetric on $\mathcal A(X)$ satisfying Axiom 3. Let $\mu$ be the measure on $2^X$ whose point masses are $\mu\{b\}=d(\succsim_{ab},\succsim^+_{ab})$ for every $a\ne b$ (assumed to be independent of $a$, which Lemma 3.4 guarantees under Axiom 1). Then for every acyclic order $\succsim$ and distinct $a,b\in X$:
--
--   1. if $a,b$ are not $\succ$-comparable and $\succsim\oplus(a,b)$ is acyclic, $d(\succsim,\succsim\oplus(a,b))=D^\mu(\succsim,\succsim\oplus(a,b))$;
--   2. if $a\succ b$, $d(\succsim,\succsim\ominus(a,b))=D^\mu(\succsim,\succsim\ominus(a,b))$.
--
--   In words, $d$ and $D^\mu$ have the same value at every pair $(\succsim,\trianglerighteq)$ in which $\trianglerighteq$ is a one-step perturbation of $\succsim$:
--   $$d(\succsim,\trianglerighteq)=D^\mu(\succsim,\trianglerighteq).$$
--
--   This is the base case of the "only if" direction of Theorem 3.1.
--
--   **Formalization Note** $\mu$ is given by point weights `w` with the hypothesis $w(b)=d(\succsim_{ab},\succsim^+_{ab})$ for all $a\ne b$; this is the page's definition $\mu\{b\}=m_b$, with its well-definedness (Lemma 3.4) taken as part of the hypothesis.
-- source:
--   Nishimura & Ok, A Class of Dissimilarity Semimetrics for Preference Relations, arXiv:2203.04418v1, p. 17, §3.3, proof of Theorem 3.1 (definition of mb and µ; 'Conclusion: d and Dµ have the same value at (≿, ⊵) for every ≿, ⊵ ∈ A(X) where ⊵ is a one-step perturbation of ≿.')

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

namespace PrefSemimetric.TopDiff

theorem agree_single_perturbation {X : Type*} [Fintype X] [DecidableEq X]
    (d : (X → X → Prop) → (X → X → Prop) → ℝ) (hd : IsSemimetric d) (h3 : Axiom3 d)
    (w : X → ℝ) (hw : ∀ a b, a ≠ b → w b = d (prefAB a b) (prefABplus a b))
    (R : X → X → Prop) (hR : IsAcyclicOrder R) (a b : X) (hab : a ≠ b) :
    (¬ asymmPart R a b → ¬ asymmPart R b a → IsAcyclicOrder (oplus R a b) →
        d R (oplus R a b) = Dmu w R (oplus R a b)) ∧
      (asymmPart R a b → d R (ominus R a b) = Dmu w R (ominus R a b)) := by sorry

end PrefSemimetric.TopDiff

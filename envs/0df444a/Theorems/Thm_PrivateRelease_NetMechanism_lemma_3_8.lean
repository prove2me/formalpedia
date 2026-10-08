-- Prove2me | Theorems.Thm_PrivateRelease_NetMechanism_lemma_3_8
-- name    : PrivateRelease.NetMechanism.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:45.109452+00:00
-- url     : https://prove2.me/theorems/f00d1997-a929-4d58-bc0d-bcfcbb6e9ac7
-- title:
--   Lemma 3.8 [AB99, Vap98] — a database of size O(VCDIM(C) log(1/α)/α²) approximates every database on C
-- statement:
--   There is an absolute constant $c_0>0$ with the following property. Let $X$ be any data universe, $C$ a class of predicates $\varphi:X\to\{0,1\}$ of finite VC-dimension $d\ge1$, and $0<\alpha\le\tfrac12$. For every (nonempty) database $D\in X^*$ there is a database $D'\in X^*$ with
--   $$
--   |D'|\ \le\ c_0\,\frac{d\,\log(1/\alpha)}{\alpha^2}
--   $$
--   such that $|Q_\varphi(D)-Q_\varphi(D')|\le\alpha$ for every $\varphi\in C$.
--
--   This is the uniform-convergence (ε-approximation) property of classes of finite VC-dimension, which the paper cites from Anthony–Bartlett and Vapnik; it replaces Lemma 3.7 for infinite classes.
--
--   **Formalization Note** The paper writes $|D'|=O(\mathrm{VCDIM}(C)\log(1/\alpha)/\alpha^2)$; the $O(\cdot)$ is an absolute constant $c_0$ quantified before the universe, the class and $\alpha$, and the size is "at most". The VC-dimension is the platform's `HighDimProb.Chaining.vcDim`. The cases $d=0$ (the bound is $0$, while $D'$ is nonempty) and $\alpha>\tfrac12$ (where $\log(1/\alpha)$ may be $\le0$) are excluded. Logarithms are natural.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 10, Lemma 3.8 (citing Anthony–Bartlett 1999, Vapnik 1998)

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_PrivateRelease_NetMechanism_Queries

namespace PrivateRelease.NetMechanism

/-- Lemma 3.8 ([AB99, Vap98], p. 10): there is an absolute constant `c₀ > 0` such that for every
data universe `X`, every class `C` of predicates of finite VC-dimension `d ≥ 1`, every
`0 < α ≤ 1/2` and every database `D ∈ X*`, some database `D′` of size at most
`c₀ d log(1/α)/α²` has `|Q_φ(D) − Q_φ(D′)| ≤ α` for every `φ ∈ C`. -/
theorem lemma_3_8 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (X : Type) (C : Set (X → Bool)) (d : ℕ) (α : ℝ),
      HighDimProb.Chaining.vcDim C = (d : ℕ∞) → 1 ≤ d → 0 < α → α ≤ 1 / 2 →
      ∀ D : Database X, ∃ D' : Database X,
        (Multiset.card D'.1 : ℝ) ≤ c₀ * d * Real.log (1 / α) / α ^ 2 ∧
          ∀ φ ∈ C, |countQ φ D.1 - countQ φ D'.1| ≤ α := by sorry

end PrivateRelease.NetMechanism

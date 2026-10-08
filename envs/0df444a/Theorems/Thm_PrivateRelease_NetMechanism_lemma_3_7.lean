-- Prove2me | Theorems.Thm_PrivateRelease_NetMechanism_lemma_3_7
-- name    : PrivateRelease.NetMechanism.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:55.143109+00:00
-- url     : https://prove2.me/theorems/4062c7d3-5313-43e1-946a-e084c8f30cb3
-- title:
--   Lemma 3.7 — a database of size ⌈log|C|/α²⌉ approximates every database on a finite class C
-- statement:
--   Let $X$ be a data universe and $C$ a finite class of at least three predicates $\varphi:X\to\{0,1\}$, and let $\alpha>0$. For every (nonempty) database $D\in X^*$ there is a database $D'\in X^*$ of size
--   $$
--   |D'|=\left\lceil\frac{\log|C|}{\alpha^2}\right\rceil
--   $$
--   such that $|Q_\varphi(D)-Q_\varphi(D')|\le\alpha$ for every $\varphi\in C$.
--
--   The size does not depend on $|D|$; this is what bounds the size of α-nets for finite classes (Theorem 3.6).
--
--   **Formalization Note** The paper's size $\log|C|/\alpha^2$ must be an integer and is rounded up. The paper's proof needs $|C|>2$ ("so long as $|C|>2$"), which is the hypothesis $|C|\ge3$; for $|C|=1$ the size would be $0$. Logarithms are natural.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 9, Lemma 3.7

import Mathlib
import Definitions.Def_PrivateRelease_NetMechanism_Queries

namespace PrivateRelease.NetMechanism

/-- Lemma 3.7 (p. 9): for any database `D ∈ X*` and any finite class `C` of at least three
counting queries, there is a database `D′` of size `⌈log|C|/α²⌉` with
`|Q_φ(D) − Q_φ(D′)| ≤ α` for every `φ ∈ C`. -/
theorem lemma_3_7 {X : Type} (C : Finset (X → Bool)) (α : ℝ) (hC : 3 ≤ C.card) (hα : 0 < α)
    (D : Database X) :
    ∃ D' : Database X, Multiset.card D'.1 = ⌈Real.log (C.card : ℝ) / α ^ 2⌉₊ ∧
      ∀ φ ∈ C, |countQ φ D.1 - countQ φ D'.1| ≤ α := by sorry

end PrivateRelease.NetMechanism

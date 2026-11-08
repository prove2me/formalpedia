-- Prove2me | Theorems.Thm_QWildMatch_lemma_3_1
-- name    : QWildMatch.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:17:03.738243+00:00
-- url     : https://prove2.me/theorems/02df9066-6f44-44e4-84fb-d1fde96157f9
-- title:
--   Lemma 3.1 — length restriction of an alignment of cost at most $k$
-- statement:
--   Let $P$ be a pattern of length $m$, let $w=T[s:e]$ be a word, and consider an alignment of $P$ with $w$ of cost at most $k$, with $r$ inserted and $d$ deleted symbols. Then
--
--   $$r\le r_+=\lfloor k/\alpha\rfloor,\qquad d\le r_-=\lfloor k/\beta\rfloor,\qquad m-r_-\le e-s\le m+r_+.$$
--
--   Moreover, at each prefix of the alignment, if $i$ pattern symbols and $u$ text symbols have been consumed, then $-r_-\le u-i\le r_+$.
--
--   This lemma confines every accepting alignment to a band of the alignment grid, which is what makes the dynamic program of Theorem 4.1 local.
--
--   **Formalization Note** The alignment is an edge list of cost at most $k$ in `WithTop ℝ`, and differences are in $\mathbb Z$. No hypothesis $k\ge0$ is needed, because a path of cost at most $k$ forces it.
--
--   Differences from the source:
--   - generalization: §3 fixes $\mu(\star,b)=0$ and $\mu(a,a)=0$ → Lean takes any $\mu\ge0$; reason: the lemma uses neither equation, and a table satisfying them is an instance.
--   - encoding: an alignment of $P$ with $T[s:e]$, with $e-s$ its text length → an edge list for a word $w$, with $e-s$ the length of $w$; reason: every word is a substring of itself and every substring is a word, so the instances are the same.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), Lemma 3.1, p.4

import Mathlib
import Definitions.Def_QWildMatch_pathCost

namespace QWildMatch

/-- Lemma 3.1 (Length restriction), Zhao et al., STOC 2027 submission (file sha256 9e87a9dd…), p.4.

**Formalization Note** The alignment is an edge list `o` of finite cost at most `k` from `(0, s)` to
`(m, e)`, with `w = T[s : e]`, so `e − s` is `w.length`. Differences are in `ℤ`. No `k ≥ 0` is needed:
a path of cost at most `k` forces it. -/
theorem lemma_3_1 {Sym : Type} [Fintype Sym] [Nonempty Sym] (cm : CostModel Sym)
    (P : List (Option Sym)) (w : List Sym) (k : ℝ) (o : List Op)
    (ho : pathCost cm P w o ≤ ((k : ℝ) : WithTop ℝ)) :
    o.count Op.ins ≤ rPlus cm k ∧
    o.count Op.del ≤ rMinus cm k ∧
    (P.length : ℤ) - (rMinus cm k : ℤ) ≤ (w.length : ℤ) ∧
    (w.length : ℤ) ≤ (P.length : ℤ) + (rPlus cm k : ℤ) ∧
    ∀ t : ℕ, t ≤ o.length →
      -(rMinus cm k : ℤ) ≤ (textConsumed (o.take t) : ℤ) - (patternConsumed (o.take t) : ℤ) ∧
      (textConsumed (o.take t) : ℤ) - (patternConsumed (o.take t) : ℤ) ≤ (rPlus cm k : ℤ) := by sorry

end QWildMatch

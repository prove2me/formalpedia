-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_Supplement_lemma_3_5
-- name    : QMomentMatch.FirstBound.Supplement.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:41:40.891964+00:00
-- url     : https://prove2.me/theorems/edfb1728-e479-423e-983c-9ea032628188
-- title:
--   Lemma 3.5 — Lagrange interpolation on integer nodes in $\{0,\dots,A\}$ and $\sum_i|L_i(t)|\le4^{A-1}$ at integers $t$
-- statement:
--   Let $A\ge2$ and $0\le d\le A$ be integers and let $s_0<s_1<\dots<s_d$ be integers in $\{0\}\cup[A]=\{0,1,\dots,A\}$. Define the Lagrange basis polynomials
--   $$L_i(x)=\prod_{\substack{0\le h\le d\\ h\ne i}}\frac{x-s_h}{s_i-s_h}\qquad(0\le i\le d).$$
--
--   1. Every real polynomial $P$ of degree at most $d$ satisfies $P(x)=\sum_{i=0}^{d}P(s_i)L_i(x)$ for all real $x$.
--   2. At every integer $t\in\{0\}\cup[A]$,
--   $$\sum_{i=0}^{d}|L_i(t)|\le4^{A-1}.$$
--
--   The bound on the Lebesgue function at integer points is the step of Lemma 4.2's proof that produces its factor $32^{-A}$.
--
--   Differences from the source:
--   - encoding: nodes s_0 < ⋯ < s_d in {0} ∪ [A] → s : Fin (d + 1) → ℕ, StrictMono s, s i ≤ A; reason: same data
--   - encoding: P(x) = Σ P(s_i) L_i(x) → equality of evaluations at every real x; reason: polynomial identity over ℝ is equality at every real point
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Lemma 3.5, p. 17 (proof: Appendix A, p. 44)

import Mathlib

namespace QMomentMatch.FirstBound.Supplement

open Polynomial

/-- Lemma 3.5 (Lagrange interpolation), p. 17 (proof: Appendix A, p. 44). Nodes
`s_0 < ⋯ < s_d` in `{0} ∪ [A]` and `L_i(x) = ∏_{h ≠ i} (x − s_h)/(s_i − s_h)`. -/
theorem lemma_3_5 (A d : ℕ) (hA : 2 ≤ A) (hd : d ≤ A) (s : Fin (d + 1) → ℕ)
    (hs : StrictMono s) (hsA : ∀ i, s i ≤ A) :
    (∀ P : ℝ[X], P.natDegree ≤ d → ∀ x : ℝ,
      P.eval x = ∑ i, P.eval (s i : ℝ) *
        ∏ h ∈ Finset.univ.erase i, (x - (s h : ℝ)) / ((s i : ℝ) - (s h : ℝ))) ∧
    (∀ t : ℕ, t ≤ A →
      ∑ i, |∏ h ∈ Finset.univ.erase i, ((t : ℝ) - (s h : ℝ)) / ((s i : ℝ) - (s h : ℝ))| ≤
        (4 : ℝ) ^ (A - 1)) := by sorry

end QMomentMatch.FirstBound.Supplement

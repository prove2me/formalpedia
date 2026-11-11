-- Prove2me | Theorems.Thm_SubexpPermanent_Main_lemma_6_3
-- name    : SubexpPermanent.Main.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:02:56.435139+00:00
-- url     : https://prove2.me/theorems/0248ea70-873f-40d2-8fd8-d7304453b0cc
-- title:
--   Lemma 6.3 — at any minimizer some vertex is tight, $d\le\sqrt2\,n e^{-a/2}$, and $0\le\mathrm{OPT}_A(a)-\mathrm{OPT}_A(b)\le(b-a)d$
-- statement:
--   Let $A$ be a nonnegative real $n\times n$ matrix with $\operatorname{per}(A)>0$. Fix $a\in\mathbb R$ and let $y$ be any minimizer of $\Phi_A$ over $D_a$. Let $d=n-\sum_e\mu_{y,e}$, the expected number of unmatched rows in a matching drawn from $\nu_{G,e^y}$. Then $\sum_{e\ni v}e^{y_e}=e^a$ for some vertex $v$, and
--   $$d\le\sqrt2\,n\,e^{-a/2}\qquad(21).$$
--   For every $b>a$,
--   $$0\le\mathrm{OPT}_A(a)-\mathrm{OPT}_A(b)\le(b-a)\,d\qquad(22).$$
--   Integrating (22) with (21) over $[a,\infty)$ gives the error bound of Lemma 6.1.
--
--   Differences from the source:
--
--   - encoding: an n × n matrix (n a positive integer) → hypothesis 1 ≤ n; reason: the dimension of a matrix is positive; the §6 objects H(x) (a maximum over vertices) and 'some vertex' need a vertex
--   - encoding: vectors in ℝ^E indexed by the edges of E → functions on the subtype Edges A of pairs (i, j) in E; reason: the same space with the same coordinates
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 21, Lemma 6.3, eqs. (21)–(22)

import Mathlib
import Definitions.Def_SubexpPermanent_Main_Objective

namespace SubexpPermanent.Main

/-- Lemma 6.3 (unmatched rows and decrease in the optimum), p. 21. -/
theorem lemma_6_3 {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hper : 0 < A.permanent) (a : ℝ) (y : Edges A → ℝ) (hy : y ∈ budgetSet A a)
    (hmin : ∀ y' ∈ budgetSet A a, Phi A y ≤ Phi A y') :
    let d : ℝ := (n : ℝ) - ∑ e, edgeProbA A y e
    (∃ v : Fin n ⊕ Fin n, vertexSum A y v = Real.exp a) ∧
    d ≤ Real.sqrt 2 * n * Real.exp (-a / 2) ∧
    ∀ b : ℝ, a < b → 0 ≤ OPT A a - OPT A b ∧ OPT A a - OPT A b ≤ (b - a) * d := by sorry

end SubexpPermanent.Main

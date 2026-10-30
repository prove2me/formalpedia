-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P49_rectangularMutualCovering
-- name    : QAlgorithms.Papers.Independent.Extend50.P49.rectangularMutualCovering
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:23:52.169691+00:00
-- url     : https://prove2.me/theorems/fa3ad071-6eaf-4a7c-ba67-019d5ba2f2d7
-- title:
--   Rectangular mutual covering with row and column dependencies
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space, let $r,s$ be positive integers, and let $\alpha>0$ and $0<q\le1$. For $1\le k\le r$ and $1\le\ell\le s$, let $J_{k\ell}:\Omega\to\{0,1\}$ be measurable. Assume
--   $$\begin{aligned}\mathbb E J_{k\ell}&\ge\alpha q,\\\mathbb E[J_{k\ell}J_{k\ell'}]&\le q^2&& (\ell\ne\ell'),\\\mathbb E[J_{k\ell}J_{k'\ell}]&\le q^2&& (k\ne k').\end{aligned}$$
--   Assume only that $J_{k\ell}$ and $J_{k'\ell'}$ are independent whenever both $k\ne k'$ and $\ell\ne\ell'$. Define $Z=\sum_{k=1}^r\sum_{\ell=1}^sJ_{k\ell}$. Then
--   $$\Pr\{Z=0\}\le\frac1{\alpha rsq}+\frac{r+s}{\alpha^2rs}.$$
--   This covering estimate allows dependencies within a row or column. Measurable bounded variables on a normalized probability space are integrable, so the expectations have their usual values.
-- source:
--   One-shot Marton inner bound for classical-quantum broadcast channel, arXiv:1410.3248v5, PDF p. 15, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P49

open QAlgorithms MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 1, PDF p.15: rectangular mutual covering with exactly the stated pairwise
independence away from common rows and columns. Positive alpha,r,s are the denominator
domain implicit in the source proof. No full joint independence is assumed. -/
theorem rectangularMutualCovering {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (alpha q : ℝ) (hAlpha : 0 < alpha) (hq : 0 < q ∧ q ≤ 1)
    (J : Fin r → Fin s → Omega → ℝ)
    (hMeasurable : ∀ k l, Measurable (J k l))
    (hBinary : ∀ k l w, J k l w = 0 ∨ J k l w = 1)
    (hMean : ∀ k l, alpha * q ≤ ∫ w, J k l w ∂mu)
    (hRow : ∀ k l l2, l ≠ l2 → (∫ w, J k l w * J k l2 w ∂mu) ≤ q ^ 2)
    (hColumn : ∀ k k2 l, k ≠ k2 → (∫ w, J k l w * J k2 l w ∂mu) ≤ q ^ 2)
    (hIndependent : ∀ k k2 l l2, k ≠ k2 → l ≠ l2 →
      ProbabilityTheory.IndepFun (J k l) (J k2 l2) mu) :
    (mu {w | (∑ k, ∑ l, J k l w) = 0}).toReal ≤
      1 / (alpha * r * s * q) + ((r : ℝ) + s) / (alpha ^ 2 * r * s) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P49

end

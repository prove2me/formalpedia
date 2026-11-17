-- Prove2me | Theorems.Thm_RankingCertGap_Supplement_theorem_5
-- name    : RankingCertGap.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:58:13.138556+00:00
-- url     : https://prove2.me/theorems/8f5d7fe2-868c-4389-a0d2-894cb6b1110b
-- title:
--   Theorem 5 — exact online-degree-two values, gap, unique optimizer, and Stieltjes measure
-- statement:
--   Let $s^\star$ be the unique root in $(0,1)$ of $2s^4+2s^3-8s^2-33s+7=0$. Then
--   $$
--   \Gamma(2)=\frac{2}{3-s^\star},\qquad
--   \gamma(2)=1-\sum_{k=1}^{\infty}2^{-(2^k+k-1)},
--   $$
--   $$
--   \Delta(2)=1-\sum_{k=1}^{\infty}2^{-(2^k+k-1)}-\frac{2}{3-s^\star}.
--   $$
--   Writing $w^\star=2/((1-s^\star)(3-s^\star))$, the unique optimizer is $0$ below $s^\star$, $w^\star$ on $[s^\star,1)$, and $1$ at $1$. Its Stieltjes measure is
--   $$
--   \pi_{f^\star_2}=w^\star\delta_{s^\star}+(1-w^\star)\delta_1.
--   $$
--
--   This gives the complete exact result at online degree at most two, including both the optimized certificate and RANKING's larger worst-case value.
--
--   **Formalization Note** The series is the published `cStar`, whose index is shifted to start at zero without changing the exponent. Optimizer equality is on $[0,1]$.
--
--   Differences from the source:
--   - encoding: $s^\star$ as the unique root in $(0,1)$ → the infimum of the root set together with explicit membership, roothood, and uniqueness clauses; reason: the clauses identify the same unique root and prevent the empty-infimum convention from surviving
--   - encoding: $\sum_{k=1}^{\infty}2^{-(2^k+k-1)}$ → $\sum_{k=0}^{\infty}(1/2)^{2^{k+1}+k}$; reason: an index shift removes natural-number subtraction and is term-for-term identical
--   - encoding: profiles and Stieltjes measures on $[0,1]$ → total real profiles and probability measures on $\mathbb R$ identified by their lower-interval values on $[0,1]$; reason: the extensions and ambient carrier change no source instance
--   - encoding: unique optimizer on $[0,1]$ → equality at every point of $[0,1]$; reason: values outside the source domain are irrelevant
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Theorem 5, pp.8–9, eqs. (18)–(22)

import Mathlib
import Definitions.Def_RankingCertGap_Supplement_Objects
import Definitions.Def_RankingCertGap_SafetyState

set_option autoImplicit false

open MeasureTheory

namespace RankingCertGap.Supplement

/-- **Theorem 5 (Online degree at most two: exact values and gap).** Xu, arXiv:2610.17545
(held file sha256 75896dd9…), Theorem 5, pp.8–9, eqs. (18)–(22). The unique root `s★`, the
exact capacity, competitiveness and gap, the unique step-profile optimizer, and its Stieltjes
measure are all included.

**Formalization Note.** `cStar` is definitionally
`1 - ∑' k : ℕ, (1/2)^(2^(k+1)+k)`, the source series after shifting its index from `k ≥ 1`.
Optimizer equality is pointwise on `[0,1]`. The Stieltjes-measure coefficients use `ENNReal.ofReal`;
the root and optimizer clauses imply they are the printed nonnegative weights. -/
theorem theorem_5 :
    sStar ∈ Set.Ioo (0 : ℝ) 1 ∧
    rootPoly sStar = 0 ∧
    (∀ s ∈ Set.Ioo (0 : ℝ) 1, rootPoly s = 0 → s = sStar) ∧
    GammaC classF (onDegLE 2) = 2 / (3 - sStar) ∧
    gammaC (onDegLE 2) = cStar ∧
    gapC classF (onDegLE 2) = cStar - 2 / (3 - sStar) ∧
    fStar ∈ classF ∧
    chiC fStar (onDegLE 2) = GammaC classF (onDegLE 2) ∧
    (∀ f : ℝ → ℝ, f ∈ classF →
      chiC f (onDegLE 2) = GammaC classF (onDegLE 2) →
      ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = fStar y) ∧
    HasStieltjesMeasure fStar
      (ENNReal.ofReal wStar • Measure.dirac sStar +
        ENNReal.ofReal (1 - wStar) • Measure.dirac (1 : ℝ)) := by sorry

end RankingCertGap.Supplement

-- Prove2me | Theorems.Thm_PostTruth_Regimes_bayes_necessary
-- name    : PostTruth.Regimes.bayes_necessary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:35.648927+00:00
-- url     : https://prove2.me/theorems/a4507d97-ad2f-4164-8a7e-825764ece055
-- title:
--   Proof of Theorem 1 — a necessary misinformation level for Bayesian mislearning
-- statement:
--   Let $1/2<p\leq1$ and $0<q<1/2$. Suppose the split density is positive on its support interval $[\underline r,\overline r]\subseteq[0,1]$ and vanishes outside, and the realized split $r$ belongs to that interval. The prior-belief law $H$ need not have full support. If the true state is $L$ and the Bayesian society mislearns at $r$, then
--
--   $$
--   q\geq\frac{2p-1}{2p-\underline r}\geq q^* = \frac{2p-1}{2p}.
--   $$
--
--   In probability, as the page states it: if the Bayesian society mislearns with positive $F$-probability when the true state is $L$, then
--
--   $$
--   q>\frac{2p-1}{2p-\underline r}.
--   $$
--
--   This condition excludes Bayesian mislearning throughout the low-misinformation regime.
--
--   **Formalization Note** The page's strict $q>$ is stated for the event of positive $F$-probability. For a single realized split the strict form can fail at the endpoint $r=1$ (equality $q=(2p-1)/(2p-\underline r)$ still allows mislearning there), so the pointwise conjunct uses $q\geq$; that endpoint has zero $F$-mass. We require $r$ to be in the support to avoid the arbitrary value of a real quotient with zero denominator.
-- source:
--   Mostagir & Siderius, Learning in a Post-Truth World, SSRN working paper 3879174 (version of 2 July 2021), p. 20, proof of Theorem 1 (necessary condition); https://ssrn.com/abstract=3879174

import Mathlib
import Definitions.Def_PostTruth_Regimes_Model

namespace PostTruth.Regimes

open MeasureTheory

/-- Necessary condition in the proof of Theorem 1, p. 20. -/
theorem bayes_necessary (p q rlo rhi : ℝ) (H : Measure ℝ)
    (F : SplitLaw) (hpq : Standing p q) (hH : PriorLaw H)
    (hrlo : 0 ≤ rlo) (hwidth : rlo < rhi) (hrhi : rhi ≤ 1)
    (hF : F.FullSupportOn rlo rhi) :
    qStar p ≤ (2 * p - 1) / (2 * p - rlo) ∧
    (0 < probBayes p q H F .L → (2 * p - 1) / (2 * p - rlo) < q) ∧
    ∀ r ∈ Set.Icc rlo rhi,
      MislearnsBayes p q H F .L r → (2 * p - 1) / (2 * p - rlo) ≤ q := by sorry

end PostTruth.Regimes

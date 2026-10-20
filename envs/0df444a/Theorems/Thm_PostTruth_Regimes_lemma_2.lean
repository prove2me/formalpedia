-- Prove2me | Theorems.Thm_PostTruth_Regimes_lemma_2
-- name    : PostTruth.Regimes.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:30.382504+00:00
-- url     : https://prove2.me/theorems/df6ed639-030e-4751-b2a2-49e2888032c5
-- title:
--   Lemma 2 — Bayesian mislearning cutoffs with full prior support
-- statement:
--   Let $1/2<p\leq1$ and $0<q<1/2$. Suppose the density of the split has full support on $[\underline r,\overline r]\subseteq[0,1]$, and the continuous prior law $H$ has full support on $[0,1]$. Put $d=(2p-1)(1-q)/q$. For every realized split $r$ in the support,
--
--   $$
--   \theta=L:\quad \text{Bayes mislearns}\iff r\geq\underline r+d,
--   \qquad
--   \theta=R:\quad \text{Bayes mislearns}\iff r\leq\overline r-d.
--   $$
--
--   The two cutoffs identify precisely when a second, incorrect narrative is feasible and some agents give it enough weight to take the wrong action.
--
--   **Formalization Note** The paper says only that $H$ has full support on its own interval. The converse requires beliefs arbitrarily near 0 and 1, so this statement assumes full support on $[0,1]$. The realized split is restricted to the support, where the true narrative has positive density.
-- source:
--   Mostagir & Siderius, Learning in a Post-Truth World, SSRN working paper 3879174 (version of 2 July 2021), p. 19, Lemma 2 and its proof; https://ssrn.com/abstract=3879174

import Mathlib
import Definitions.Def_PostTruth_Regimes_Model

namespace PostTruth.Regimes

open MeasureTheory

/-- Mostagir–Siderius, Lemma 2, p. 19, with the needed full-support domain made explicit. -/
theorem lemma_2 (p q rlo rhi : ℝ) (H : Measure ℝ)
    (F : SplitLaw) (hpq : Standing p q) (hH : PriorLaw H)
    (hHfull : PriorFullSupportOn H 0 1)
    (hrlo : 0 ≤ rlo) (hwidth : rlo < rhi) (hrhi : rhi ≤ 1)
    (hF : F.FullSupportOn rlo rhi) :
    ∀ r ∈ Set.Icc rlo rhi,
      (MislearnsBayes p q H F .L r ↔ rlo + gap p q ≤ r) ∧
      (MislearnsBayes p q H F .R r ↔ r ≤ rhi - gap p q) := by sorry

end PostTruth.Regimes

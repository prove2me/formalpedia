-- Prove2me | Theorems.Thm_PostTruth_Regimes_lemma_1
-- name    : PostTruth.Regimes.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:31.806517+00:00
-- url     : https://prove2.me/theorems/4394b9a4-e5e1-4c3d-a211-5b3a0edf87d4
-- title:
--   Lemma 1 — DeGroot mislearning cutoffs in the two states
-- statement:
--   Let $1/2<p\leq1$ and $0<q<1/2$. Let the continuous law $H$ of initial beliefs on $[0,1]$ be symmetric about $1/2$. For each realized misinformation split $r$, the DeGroot society mislearns precisely on the following sides of its state-dependent cutoff:
--
--   $$
--   \theta=L:\quad r\geq\frac{1-2(1-q)(1-p)}{2q},
--   \qquad
--   \theta=R:\quad r\leq\frac{1-2(1-q)p}{2q}.
--   $$
--
--   The cutoffs turn the consensus condition into events whose probabilities can be compared with Bayesian mislearning.
--
--   **Formalization Note** A belief exactly equal to $1/2$ counts as wrong, as the weak inequalities in the printed lemma require. The statement is pointwise in $r$, including values outside the support of $F$.
-- source:
--   Mostagir & Siderius, Learning in a Post-Truth World, SSRN working paper 3879174 (version of 2 July 2021), p. 18, Lemma 1; https://ssrn.com/abstract=3879174

import Mathlib
import Definitions.Def_PostTruth_Regimes_Model

namespace PostTruth.Regimes

open MeasureTheory

/-- Mostagir–Siderius, Lemma 1, p. 18 of the SSRN preprint. -/
theorem lemma_1 (p q : ℝ) (H : Measure ℝ)
    (hpq : Standing p q) (hH : PriorLaw H) (hSym : Symmetric H) :
    ∀ r : ℝ,
      (MislearnsDeGroot p q H .L r ↔ rTilde p q ≤ r) ∧
      (MislearnsDeGroot p q H .R r ↔ r ≤ rTildeR p q) := by sorry

end PostTruth.Regimes

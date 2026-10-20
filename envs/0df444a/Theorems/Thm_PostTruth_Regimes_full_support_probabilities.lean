-- Prove2me | Theorems.Thm_PostTruth_Regimes_full_support_probabilities
-- name    : PostTruth.Regimes.full_support_probabilities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:37.678906+00:00
-- url     : https://prove2.me/theorems/9d6e9a6f-b305-4337-bdf6-d2ac7c29cbac
-- title:
--   Proof of Theorem 1 — mislearning probabilities under full support
-- statement:
--   Let $1/2<p\leq1$ and $q^*<q<1/2$. Let $H$ be a continuous prior law symmetric about $1/2$ and fully supported on $[0,1]$, and let the split law $F$ have a positive density throughout $[0,1]$. With $d=(2p-1)(1-q)/q$, the Bayesian and DeGroot mislearning probabilities are
--
--   $$
--   \begin{aligned}
--   \theta=L:&\quad P_B=F([d,\infty)),\quad P_D=F([\widetilde r_L,\infty)),\\
--   \theta=R:&\quad P_B=F(({-\infty},1-d]),\quad P_D=F(({-\infty},\widetilde r_R]).
--   \end{aligned}
--   $$
--
--   These formulas turn the probability comparison in Theorem 1 into a comparison of cutoffs under the same split law.
--
--   **Formalization Note** The paper displays the $L$ case as $1-F(t)$; the formal statement uses the measure of a closed tail. The endpoint has zero mass because $F$ has a density. The $R$ case is the mirrored calculation.
-- source:
--   Mostagir & Siderius, Learning in a Post-Truth World, SSRN working paper 3879174 (version of 2 July 2021), p. 20, proof of Theorem 1 (part ii); https://ssrn.com/abstract=3879174

import Mathlib
import Definitions.Def_PostTruth_Regimes_Model

namespace PostTruth.Regimes

open MeasureTheory

/-- The mislearning-probability formulas in the proof of Theorem 1, p. 20. -/
theorem full_support_probabilities (p q : ℝ) (H : Measure ℝ)
    (F : SplitLaw) (hpq : Standing p q)
    (hH : PriorLaw H) (hSym : Symmetric H)
    (hHfull : PriorFullSupportOn H 0 1)
    (hF : F.FullSupportOn 0 1) (hq : qStar p < q) :
    probBayes p q H F .L = F.law (Set.Ici (gap p q)) ∧
    probDeGroot p q H F .L = F.law (Set.Ici (rTilde p q)) ∧
    probBayes p q H F .R = F.law (Set.Iic (1 - gap p q)) ∧
    probDeGroot p q H F .R = F.law (Set.Iic (rTildeR p q)) := by sorry

end PostTruth.Regimes

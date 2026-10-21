-- Prove2me | Theorems.Thm_PrefRobustSR_WorstCase_theorem_2_1
-- name    : PrefRobustSR.WorstCase.theorem_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:36.829096+00:00
-- url     : https://prove2.me/theorems/1b33f864-1bf1-4f6f-9516-e4dbb97d21df
-- title:
--   Theorem 2.1, p. 6: preference robust shortfall risk representation
-- statement:
--   Fix a probability space $(\Omega,\mathcal B,P)$ and an exponent $1\le p<\infty$. For every position $Z\in\mathcal L_p(P)$ and every set $L\subseteq\mathcal L$ of admissible loss functions,
--   $$
--   SR_L^P(Z)=\sup_{l\in L}SR_l^P(Z)
--   =\varrho_{\mathcal R_L}(Z),\qquad
--   \mathcal R_L=\{SR_l^P:l\in L\}.
--   $$
--   Conversely, for a set $\mathcal R$ of normalized convex utility-based shortfall risk measures, let $L_{\mathcal R}=\{l\in\mathcal L:SR_l^P\in\mathcal R\}$. Then
--   $$
--   \varrho_{\mathcal R}(Z)=SR_{L_{\mathcal R}}^P(Z).
--   $$
--   The theorem identifies a single robust expected-loss constraint with taking the worst risk across admissible loss functions, and connects it to the paper's risk-measure formulation.
--
--   **Formalization Note** The converse represents a normalized convex utility-based shortfall risk measure as a map equal to $SR_l^P$ for some $l\in\mathcal L$, the class characterized by Proposition 2.1; that proposition is outside this mission. Risks take extended-real values to retain the paper's possible $+\infty$ case. The risk maps are total on real functions, but these identities are asserted only for $Z\in\mathcal L_p$. The empty $L$ is allowed and both sides are $-\infty$.
-- source:
--   Delage, Guo & Xu, Shortfall risk models when information of loss function is incomplete, preprint dated April 25, 2018 (later article DOI: https://doi.org/10.1287/opre.2021.2212; numbering follows the preprint), p. 6, Theorem 2.1; converse explained on p. 8

import Mathlib
import Definitions.Def_PrefRobustSR_WorstCase_Model

namespace PrefRobustSR.WorstCase

open MeasureTheory
open scoped ENNReal

/-- Theorem 2.1, p. 6: preference robust shortfall risk is the
worst shortfall risk over the loss set, with both risk-measure representations. -/
theorem theorem_2_1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    (∀ L : Set (ℝ → ℝ), L ⊆ LossClass →
      ∀ Z : Ω → ℝ, MemLp Z p P →
        SRL P L Z = (⨆ l ∈ L, SR P l Z) ∧
        SRL P L Z = robustRisk ((fun l => SR P l) '' L) Z) ∧
    (∀ R : Set ((Ω → ℝ) → EReal),
      R ⊆ (fun l => SR P l) '' LossClass →
      ∀ Z : Ω → ℝ, MemLp Z p P →
        robustRisk R Z = SRL P {l | l ∈ LossClass ∧ SR P l ∈ R} Z) := by sorry

end PrefRobustSR.WorstCase

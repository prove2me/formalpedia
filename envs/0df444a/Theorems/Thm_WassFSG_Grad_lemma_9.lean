-- Prove2me | Theorems.Thm_WassFSG_Grad_lemma_9
-- name    : WassFSG.Grad.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:29:29.602123+00:00
-- url     : https://prove2.me/theorems/14c8c814-4c67-42f1-906c-3ce4502babd7
-- title:
--   Lemma 9 (p = 2) — under T₂(τ) and Assumption 2, w.p. ≥ 1 − e^{−t}, E_{P_true}f ≤ E_{P_n}f + R_{⊗,2}(√(τt/n); −F) + 2E_⊗[𝔑_n(F)]
-- statement:
--   Let $\mathcal Z$ be a separable Banach space, let $\mathbb P_{\mathrm{true}}$ satisfy $T_2(\tau)$, and let $\mathcal F$ satisfy Assumption 2 with constant $\hbar>0$. Let $t>0$ and $n\ge1$. Then with probability at least $1-e^{-t}$ over the sample $z_1,\dots,z_n\sim\mathbb P_{\mathrm{true}}$, for every $f\in\mathcal F$,
--   $$
--   \mathbb E_{\mathbb P_{\mathrm{true}}}[f]\le\mathbb E_{\mathbb P_n}[f]+\mathcal R_{\otimes,2}\Big(\sqrt{\tfrac{\tau t}{n}};-\mathcal F\Big)+2\,\mathbb E_\otimes[\mathfrak R_n(\mathcal F)].
--   $$
--
--   This is the case $p=2$ of the paper's Lemma 9: a uniform deviation bound whose transport term $\mathcal R_{\otimes,2}$ is later controlled by gradient norms (Lemma 13).
--
--   **Formalization Note** Only the case $p=2$ is stated (the case $p=1$ belongs to the sibling mission). "With probability at least $1-e^{-t}$, for every $f$" is an outer-measure bound $e^{-t}$ on the set of samples for which some $f\in\mathcal F$ violates the inequality; the inequality is in the extended reals. $\mathcal R_{\otimes,2}$ uses the infimum over $\lambda\ge0$ (the page writes min).
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 9 (case p = 2), p. 26

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Grad_Setting
import Definitions.Def_WassFSG_Grad_Rademacher

open MeasureTheory

namespace WassFSG.Grad

theorem lemma_9 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : IsT2 τ Ptrue)
    (F : Set (Z → ℝ)) (ħ : ℝ) (hF : GradLipBound ħ F) (t : ℝ) (ht : 0 < t) (n : ℕ) (hn : 0 < n) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
          (WassFSG.Lip.empMean z f : EReal) + productRegularizer Ptrue n (Real.sqrt (τ * t / n)) (WassFSG.Lip.negClass F)
            + 2 * WassFSG.Lip.expectedRad Ptrue n F)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end WassFSG.Grad

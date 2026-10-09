-- Prove2me | Theorems.Thm_WassFSG_Lip_lemma_11
-- name    : WassFSG.Lip.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:39:57.150128+00:00
-- url     : https://prove2.me/theorems/eb86c319-953c-4aef-8c77-d1e442259de6
-- title:
--   Lemma 11 — under T₁(τ), w.p. ≥ 1 − e^{−t}, E_{P_true}f ≤ E_{P_n}f + √(τt/n) sup_F ‖f‖_Lip + 2E_⊗[𝔑_n(F)]
-- statement:
--   Let $\mathbb P_{\mathrm{true}}$ satisfy $T_1(\tau)$, and let $\mathcal F$ satisfy Assumption 1(I) with constant $\gamma_1 > 0$. Let $t > 0$ and $n \ge 1$. Then with probability at least $1 - e^{-t}$ over an i.i.d. sample of size $n$,
--   $$
--   \mathbb E_{\mathbb P_{\mathrm{true}}}[f] \le \mathbb E_{\mathbb P_n}[f] + \sqrt{\frac{\tau t}{n}}\,\sup_{f\in\mathcal F}\|f\|_{\mathrm{Lip}} + 2\,\mathbb E_\otimes[\mathfrak R_n(\mathcal F)] \qquad \forall f\in\mathcal F.
--   $$
--
--   This specializes Lemma 9 to $p = 1$, where the product regularizer of a Lipschitz class is at most the radius times the largest Lipschitz norm. It is the input of the peeling argument of Lemma 12.
--
--   **Formalization Note** The uniform event is encoded as an outer-measure bound on the set of samples at which some $f\in\mathcal F$ violates the inequality. $\sup_{f\in\mathcal F}\|f\|_{\mathrm{Lip}}$ is a real supremum, bounded by $\gamma_1$ under Assumption 1(I). Standing conventions: $\mathcal Z$ is a separable real Banach space with its Borel $\sigma$-algebra, and $n\ge1$; $\mathbb E_{\mathbb P_{\mathrm{true}}}[f]$ is the Bochner integral (a Lipschitz $f$ is integrable under $\mathbb P_{\mathrm{true}}\in\mathcal P_1$).
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 11, p. 26

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting
import Definitions.Def_WassFSG_Lip_Rademacher

open MeasureTheory

namespace WassFSG.Lip

theorem lemma_11 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : IsT1 τ Ptrue)
    (F : Set (Z → ℝ)) (γ₁ : ℝ) (hF : LipBound γ₁ F) (t : ℝ) (ht : 0 < t) (n : ℕ) (hn : 0 < n) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
          (empMean z f : EReal)
            + ((Real.sqrt (τ * t / n) * ⨆ g : F, WassFSG.Conc.lipNorm (g : Z → ℝ) : ℝ) : EReal)
            + 2 * expectedRad Ptrue n F)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end WassFSG.Lip

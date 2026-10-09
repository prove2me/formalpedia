-- Prove2me | Theorems.Thm_WassFSG_Lip_lemma_9
-- name    : WassFSG.Lip.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:39:28.273757+00:00
-- url     : https://prove2.me/theorems/2cba74be-381d-4271-b114-51742c809bd3
-- title:
--   Lemma 9 (case p = 1) — w.p. ≥ 1 − e^{−t}, E_{P_true}f ≤ E_{P_n}f + R_{⊗,1}(√(τt/n); −F) + 2E_⊗[𝔑_n(F)] for all f ∈ F
-- statement:
--   Let $\mathcal Z$ be a separable Banach space, and let $\mathbb P_{\mathrm{true}}$ satisfy the transportation-information inequality $T_1(\tau)$. Let $\mathcal F$ be a class of losses satisfying Assumption 1(I) with constant $\gamma_1 > 0$, let $t > 0$ and $n\ge1$. Then, for an i.i.d. sample of size $n$ from $\mathbb P_{\mathrm{true}}$, with probability at least $1 - e^{-t}$, for every $f\in\mathcal F$,
--   $$
--   \mathbb E_{\mathbb P_{\mathrm{true}}}[f] \le \mathbb E_{\mathbb P_n}[f] + \mathcal R_{\otimes,1}\Big(\sqrt{\tfrac{\tau t}{n}};\,-\mathcal F\Big) + 2\,\mathbb E_\otimes[\mathfrak R_n(\mathcal F)].
--   $$
--
--   This is the uniform concentration bound behind the paper's local Rademacher results: the deviation of the empirical loss is controlled by a product-space Wasserstein regularizer of $-\mathcal F$ plus twice the Rademacher complexity.
--
--   **Formalization Note** Only the case $p = 1$ of the printed lemma ($p\in\{1,2\}$) is stated here. "With probability at least $1 - e^{-t}$, for every $f$" is the bound $\mathbb P_\otimes\{z : \exists f\in\mathcal F \text{ violating the inequality}\}\le e^{-t}$, with outer measure, so no measurability of the bad set is needed. $\mathbb E_{\mathbb P_{\mathrm{true}}}[f]$ is the Bochner integral, which is the true expectation because a Lipschitz $f$ is integrable under $\mathbb P_{\mathrm{true}}\in\mathcal P_1(\mathcal Z)$. The infimum in $\mathcal R_{\otimes,1}$ replaces the page's $\min$. Standing conventions: $\mathcal Z$ is a separable real Banach space with its Borel $\sigma$-algebra (the page says "Banach space"; separability and Borel are implicit in the duality and transport results it cites), and $n \ge 1$.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 9 (case p = 1), p. 26; R_{⊗,p} defined on p. 26

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting
import Definitions.Def_WassFSG_Lip_Rademacher

open MeasureTheory

namespace WassFSG.Lip

theorem lemma_9 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : IsT1 τ Ptrue)
    (F : Set (Z → ℝ)) (γ₁ : ℝ) (hF : LipBound γ₁ F) (t : ℝ) (ht : 0 < t) (n : ℕ) (hn : 0 < n) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
          (empMean z f : EReal) + productRegularizer Ptrue n (Real.sqrt (τ * t / n)) (negClass F)
            + 2 * expectedRad Ptrue n F)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end WassFSG.Lip

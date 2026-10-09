-- Prove2me | Theorems.Thm_WassFSG_Lip_lemma_7
-- name    : WassFSG.Lip.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:39:35.758969+00:00
-- url     : https://prove2.me/theorems/a82f3e51-fb6f-4ec0-a0ab-33be7c249f7a
-- title:
--   Lemma 7 — symmetrization: E_⊗ sup_{h∈H}{E_{P_true}h − E_{P_n}h} ≤ 2E_⊗[𝔑_n(H)]
-- statement:
--   Let $\mathbb P_{\mathrm{true}}$ be a probability measure on $\mathcal Z$, let $n\ge1$, and let $\mathcal H$ be a family of continuous, $\mathbb P_{\mathrm{true}}$-integrable functions $h:\mathcal Z\to\mathbb R$. For an i.i.d. sample $z_1,\dots,z_n\sim\mathbb P_{\mathrm{true}}$ with empirical distribution $\mathbb P_n$,
--   $$
--   \mathbb E_\otimes\Big[\sup_{h\in\mathcal H}\big\{\mathbb E_{\mathbb P_{\mathrm{true}}}[h] - \mathbb E_{\mathbb P_n}[h]\big\}\Big] \le 2\,\mathbb E_\otimes[\mathfrak R_n(\mathcal H)],
--   $$
--   where $\mathfrak R_n$ is the Rademacher complexity (factor $\tfrac1n$, no absolute value).
--
--   This is the symmetrization inequality; it turns the expected uniform deviation of empirical means into a Rademacher complexity, and is the last step of Lemma 9.
--
--   **Formalization Note** The page says only "a family of functions". The Lean requires each $h$ to be $\mathbb P_{\mathrm{true}}$-integrable (so $\mathbb E_{\mathbb P_{\mathrm{true}}}[h]$ is the integral) and continuous; continuity makes the suprema lower semicontinuous, hence Borel measurable, so both expectations are genuine integrals. Every class to which the paper applies the lemma consists of Lipschitz, hence continuous, losses. Both sides are extended reals ($\int\varphi^+ - \int\varphi^-$). $n\ge1$ is assumed (the statement is false at $n = 0$).
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 7, p. 25

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting
import Definitions.Def_WassFSG_Lip_Rademacher

open MeasureTheory

namespace WassFSG.Lip

theorem lemma_7 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (n : ℕ) (hn : 0 < n)
    (H : Set (Z → ℝ)) (hcont : ∀ h ∈ H, Continuous h) (hint : ∀ h ∈ H, Integrable h Ptrue) :
    ModelRiskOT.Duality.extIntegral (Measure.pi fun _ : Fin n => Ptrue)
        (fun z => ⨆ h ∈ H, ((∫ x, h x ∂Ptrue - empMean z h : ℝ) : EReal))
      ≤ 2 * expectedRad Ptrue n H := by sorry

end WassFSG.Lip

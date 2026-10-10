-- Prove2me | Theorems.Thm_WassFSG_Grad_lemma_7
-- name    : WassFSG.Grad.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:29:13.197098+00:00
-- url     : https://prove2.me/theorems/2994bbd3-43f5-4058-962e-a42315bb97ce
-- title:
--   Lemma 7 — symmetrization, E_⊗ sup_h (E_{P_true}h − E_{P_n}h) ≤ 2E_⊗[𝔑_n(H)]
-- statement:
--   Let $\mathbb P_{\mathrm{true}}$ be a probability distribution on $\mathcal Z$, let $n\ge1$, and let $\mathcal H$ be a family of continuous, $\mathbb P_{\mathrm{true}}$-integrable functions $h:\mathcal Z\to\mathbb R$. For an i.i.d. sample $z_1,\dots,z_n\sim\mathbb P_{\mathrm{true}}$ with empirical distribution $\mathbb P_n$,
--   $$
--   \mathbb E_\otimes\Big[\sup_{h\in\mathcal H}\big\{\mathbb E_{\mathbb P_{\mathrm{true}}}[h]-\mathbb E_{\mathbb P_n}[h]\big\}\Big]\le 2\,\mathbb E_\otimes[\mathfrak R_n(\mathcal H)].
--   $$
--
--   This is the standard symmetrization inequality; it converts the expected uniform deviation into a Rademacher complexity, and is the step from concentration to complexity in Lemmas 9 and 13 and in Corollary 6.
--
--   **Formalization Note** The page says only "a family of functions". Continuity (which makes every supremum here Borel in the sample) and integrability (which makes $\mathbb E_{\mathbb P_{\mathrm{true}}}[h]$ meaningful) are added, as is $n\ge1$; the statement is false at $n=0$. Both sides are extended reals.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 7, p. 25

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Grad_Setting
import Definitions.Def_WassFSG_Grad_Rademacher

open MeasureTheory

namespace WassFSG.Grad

theorem lemma_7 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (n : ℕ) (hn : 0 < n)
    (H : Set (Z → ℝ)) (hcont : ∀ h ∈ H, Continuous h) (hint : ∀ h ∈ H, Integrable h Ptrue) :
    ModelRiskOT.Duality.extIntegral (Measure.pi fun _ : Fin n => Ptrue)
        (fun z => ⨆ h ∈ H, ((∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h : ℝ) : EReal))
      ≤ 2 * WassFSG.Lip.expectedRad Ptrue n H := by sorry

end WassFSG.Grad

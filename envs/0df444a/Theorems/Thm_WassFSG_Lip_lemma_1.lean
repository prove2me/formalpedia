-- Prove2me | Theorems.Thm_WassFSG_Lip_lemma_1
-- name    : WassFSG.Lip.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:38:57.891432+00:00
-- url     : https://prove2.me/theorems/bbd4487e-719d-443e-9c4e-f42121fbf063
-- title:
--   Lemma 1 — R_{Q,1}(ρ; f) ≤ ρ‖f‖_Lip under Assumption 1(I), with equality under Assumption 1(II)
-- statement:
--   Let $\mathcal Z$ be a separable Banach space, $\mathbb Q\in\mathcal P_1(\mathcal Z)$ and $\rho\ge0$. Let $f:\mathcal Z\to\mathbb R$ satisfy Assumption 1(I): $f(\tilde z) - f(z)\le\gamma_1\|\tilde z - z\|$ for all $z,\tilde z$, for some $\gamma_1 > 0$. Then
--   $$
--   \mathcal R_{\mathbb Q,1}(\rho; f)\le\rho\cdot\|f\|_{\mathrm{Lip}}.
--   $$
--   If, in addition, Assumption 1(II) holds ($\operatorname{diam}(\mathcal Z) = \infty$ and $\limsup_{\|z-z_0\|\to\infty}(f(z)-f(z_0))/\|z-z_0\| = \|f\|_{\mathrm{Lip}}$ for some $z_0$), then
--   $$
--   \mathcal R_{\mathbb Q,1}(\rho; f) = \rho\cdot\|f\|_{\mathrm{Lip}}.
--   $$
--
--   The lemma identifies the 1-Wasserstein regularizer with Lipschitz regularization; with $\mathbb Q = \mathbb P_n$ it turns Theorem 2 into the Wasserstein DRO guarantee of Corollary 4.
--
--   **Formalization Note** The page states the lemma for every $f$ of a class $\mathcal F$ satisfying Assumption 1; here it is stated for a single $f$, i.e. for the class $\{f\}$, which is equivalent. $\mathcal R_{\mathbb Q,1}$ is valued in the extended reals, with expectations as extended integrals. Standing conventions: $\mathcal Z$ is a separable real Banach space with its Borel $\sigma$-algebra.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 1, p. 5 (proof in App. A, p. 19)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting

open MeasureTheory

namespace WassFSG.Lip

theorem lemma_1 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Q : Measure Z) (hQ : IsP1 Q) (ρ : ℝ) (hρ : 0 ≤ ρ) (f : Z → ℝ) (γ₁ : ℝ)
    (hf : LipBound γ₁ {f}) :
    regularizer Q ρ f ≤ ((ρ * WassFSG.Conc.lipNorm f : ℝ) : EReal) ∧
      (LipAttainedAtInfinity ({f} : Set (Z → ℝ)) →
        regularizer Q ρ f = ((ρ * WassFSG.Conc.lipNorm f : ℝ) : EReal)) := by sorry

end WassFSG.Lip

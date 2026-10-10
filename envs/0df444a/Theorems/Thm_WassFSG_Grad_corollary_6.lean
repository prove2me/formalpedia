-- Prove2me | Theorems.Thm_WassFSG_Grad_corollary_6
-- name    : WassFSG.Grad.corollary_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:29:41.336185+00:00
-- url     : https://prove2.me/theorems/0ad62810-a7f4-4bab-97e6-f3ee5f6cda23
-- title:
--   Corollary 6 — 2-Wasserstein DRO, w.p. ≥ 1 − (N₂+1)e^{−t}, E_{P_true}f ≤ E_{P_n}f + R_{P_n,2}(ρ̃_n; f) + 4r⋆ + 2ε_n + ħρ̃_n²
-- statement:
--   Work under the setting of Theorem 3: $\mathcal Z$ a separable Banach space, $\mathbb P_{\mathrm{true}}$ satisfying $T_2(\tau)$, $\mathcal F$ satisfying Assumption 2 with constant $\hbar>0$, $0<\|\|\nabla f\|_*\|_{\mathbb P_{\mathrm{true}},2}\le\gamma_2$ for $f\in\mathcal F$, $n\ge1$, Assumption 5 with $T(f)=\|\|\nabla f\|_*\|^2_{\mathbb P_{\mathrm{true}},2}$ and positive fixed point $r_{n\star}$, $t>0$, $\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]$ finite, and $\rho_n,\epsilon_n$ as in Theorem 3. Assume in addition that there is $\kappa_g>0$ with
--   $$
--   \frac{\|\nabla f(z)\|_*}{\|\|\nabla f\|_*\|_{\mathbb P_{\mathrm{true}},2}}\le\kappa_g\qquad\text{for all } f\in\mathcal F,\ z\in\mathcal Z,
--   $$
--   and set $\tilde\rho_n=\rho_n\big(1+2\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]+\kappa_g^2\sqrt{t/(2n)}\big)$. If
--   $$
--   2\,\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]+\kappa_g^2\sqrt{\frac{t}{2n}}<\frac12,
--   $$
--   then with probability at least $1-(N_2+1)e^{-t}$, where $N_2=\max(0,\lceil\log_2(\gamma_2\sqrt{\tau tn})\rceil)+1$, every $f\in\mathcal F$ satisfies both
--   $$
--   \mathbb E_{\mathbb P_{\mathrm{true}}}[f]\le\mathbb E_{\mathbb P_n}[f]+\tilde\rho_n\|\|\nabla f\|_*\|_{\mathbb P_n,2}+4r_{n\star}+2\epsilon_n
--   $$
--   and
--   $$
--   \mathbb E_{\mathbb P_{\mathrm{true}}}[f]\le\mathbb E_{\mathbb P_n}[f]+\mathcal R_{\mathbb P_n,2}(\tilde\rho_n;f)+4r_{n\star}+2\epsilon_n+\hbar\tilde\rho_n^2 .
--   $$
--
--   This is the paper's finite-sample guarantee for 2-Wasserstein DRO: the data-driven robust loss at a radius of order $1/\sqrt n$ upper-bounds the true loss up to an $O(1/n)$ gap, with no dependence on the dimension of $\mathcal Z$.
--
--   **Formalization Note** The page prints the probability as $1-(\lceil\log_2(\sqrt{\gamma_2\tau tn})\rceil+1)e^{-t}$; the corrected count $N_2+1$ is used (see Theorem 3 and Lemma 14; the extra $1$ is the McDiarmid event). Both displays hold on one event, stated as a conjunction inside it; the event's failure set is bounded in outer measure. The first display uses the **empirical** gradient norm $\|\|\nabla f\|_*\|_{\mathbb P_n,2}$; the second uses the 2-Wasserstein regularizer at the empirical distribution $\mathbb P_n$ of the same sample, valued in the extended reals. $\sqrt{t/2n}$ is read as $\sqrt{t/(2n)}$, as in the proof. $\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]$ enters as a real number $R_{\mathcal G}$ (finiteness is forced by the smallness condition anyway). Positivity of the gradient norms makes $\mathcal G$ and the $\kappa_g$ ratio defined; $r_{n\star}>0$ excludes the trivial fixed point $0$.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Corollary 6, pp. 11–12 (proof pp. 31–32)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Grad_Setting
import Definitions.Def_WassFSG_Grad_Rademacher

open MeasureTheory

namespace WassFSG.Grad

theorem corollary_6 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : IsT2 τ Ptrue)
    (F : Set (Z → ℝ)) (ħ : ℝ) (hF : GradLipBound ħ F)
    (hpos : ∀ f ∈ F, 0 < gradNorm Ptrue f)
    (γ₂ : ℝ) (hγ₂ : 0 < γ₂) (hbound : ∀ f ∈ F, gradNorm Ptrue f ≤ γ₂)
    (n : ℕ) (hn : 0 < n) (ψ : ℝ → ℝ) (h5 : SubRootLocalComplexity Ptrue n F ψ)
    (rstar : ℝ) (hrstar : 0 < rstar) (hfix : ψ rstar = rstar) (t : ℝ) (ht : 0 < t)
    (RG : ℝ) (hRG : WassFSG.Lip.expectedRad Ptrue n (gradClass Ptrue F) = (RG : EReal))
    (κg : ℝ) (hκg : 0 < κg)
    (hκ : ∀ f ∈ F, ∀ z : Z, ‖fderiv ℝ f z‖ / gradNorm Ptrue f ≤ κg)
    (hsmall : 2 * RG + κg ^ 2 * Real.sqrt (t / (2 * n)) < 1 / 2) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ ((∫ x, f x ∂Ptrue ≤ WassFSG.Lip.empMean z f
              + rhoTilde ħ τ t RG rstar κg n * empGradNorm z f
              + 4 * rstar + 2 * epsN ħ τ t RG n) ∧
            (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤ (WassFSG.Lip.empMean z f : EReal)
              + regularizer (WassFSG.Lip.empMeasure z) (rhoTilde ħ τ t RG rstar κg n) f
              + ((4 * rstar + 2 * epsN ħ τ t RG n
                  + ħ * rhoTilde ħ τ t RG rstar κg n ^ 2 : ℝ) : EReal)))}
      ≤ ENNReal.ofReal (((WassFSG.Lip.peelCount γ₂ τ t n : ℝ) + 1) * Real.exp (-t)) := by sorry

end WassFSG.Grad

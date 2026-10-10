-- Prove2me | Theorems.Thm_WassFSG_Grad_theorem_3
-- name    : WassFSG.Grad.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:29:18.06296+00:00
-- url     : https://prove2.me/theorems/a26b7367-86b3-4727-859b-d8a564a8204a
-- title:
--   Theorem 3 — gradient regularization, w.p. ≥ 1 − N₂e^{−t}, E_{P_true}f ≤ E_{P_n}f + ρ_n‖‖∇f‖_*‖_{P_true,2} + 4r⋆ + 2ε_n
-- statement:
--   Let $\mathcal Z$ be a separable Banach space and let $\mathbb P_{\mathrm{true}}$ satisfy $T_2(\tau)$. Let $\mathcal F$ satisfy Assumption 2 with constant $\hbar>0$, and assume there is $\gamma_2>0$ with $0<\|\|\nabla f\|_*\|_{\mathbb P_{\mathrm{true}},2}\le\gamma_2$ for all $f\in\mathcal F$. Let $n\ge1$ and let Assumption 5 hold with $T(f)=\|\|\nabla f\|_*\|^2_{\mathbb P_{\mathrm{true}},2}$: a sub-root $\psi_n$ dominates the localized Rademacher complexities, with positive fixed point $r_{n\star}$. Suppose $\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]$ is finite, let $t>0$, and set
--   $$
--   \rho_n=2\sqrt{\frac{\tau t}{n}}\big(1+\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]\big)+\sqrt{4r_{n\star}+2\epsilon_n},\qquad \epsilon_n=\frac{\hbar\tau t+1+\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]}{n}.
--   $$
--   Then with probability at least $1-N_2e^{-t}$, where $N_2=\max(0,\lceil\log_2(\gamma_2\sqrt{\tau tn})\rceil)+1$,
--   $$
--   \mathbb E_{\mathbb P_{\mathrm{true}}}[f]\le\mathbb E_{\mathbb P_n}[f]+\rho_n\|\|\nabla f\|_*\|_{\mathbb P_{\mathrm{true}},2}+4r_{n\star}+2\epsilon_n\qquad\forall f\in\mathcal F.
--   $$
--
--   When $\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]=O(1)$ and $r_{n\star}=O(1/n)$, the radius $\rho_n$ is of order $1/\sqrt n$, so gradient regularization at that radius upper-bounds the true loss up to an $O(1/n)$ gap, without dependence on the dimension of $\mathcal Z$.
--
--   **Formalization Note** The page prints the failure probability as $\lceil\log_2(\sqrt{\gamma_2\tau tn})\rceil e^{-t}$; this can be negative and does not match the proof, which applies Lemma 14 (count $\lceil\log_2(\gamma_2\sqrt{\tau tn})\rceil$, itself in need of the peeling repair). The corrected count $N_2$ is used. $r_{n\star}>0$ is required: if $\psi_n(0)=0$, then $0$ is also a fixed point, and the paper's "unique fixed point" is the positive one. Assumption 5 is required at every level $r>0$, where the page defines the localized complexity. $\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]$ enters $\rho_n$ and $\epsilon_n$ as a real number $R_{\mathcal G}$ with a hypothesis equating it to the expectation. Positivity of the gradient norms is the implicit reading that makes $\mathcal G$ defined. $\mathbb E_{\mathbb P_{\mathrm{true}}}[f]$ is the Bochner integral (integrable: Assumption 2 gives quadratic growth and $T_2(\tau)$ gives a finite second moment).
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Theorem 3, p. 11 (proof p. 31)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Grad_Setting
import Definitions.Def_WassFSG_Grad_Rademacher

open MeasureTheory

namespace WassFSG.Grad

theorem theorem_3 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : IsT2 τ Ptrue)
    (F : Set (Z → ℝ)) (ħ : ℝ) (hF : GradLipBound ħ F)
    (hpos : ∀ f ∈ F, 0 < gradNorm Ptrue f)
    (γ₂ : ℝ) (hγ₂ : 0 < γ₂) (hbound : ∀ f ∈ F, gradNorm Ptrue f ≤ γ₂)
    (n : ℕ) (hn : 0 < n) (ψ : ℝ → ℝ) (h5 : SubRootLocalComplexity Ptrue n F ψ)
    (rstar : ℝ) (hrstar : 0 < rstar) (hfix : ψ rstar = rstar) (t : ℝ) (ht : 0 < t)
    (RG : ℝ) (hRG : WassFSG.Lip.expectedRad Ptrue n (gradClass Ptrue F) = (RG : EReal)) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (∫ x, f x ∂Ptrue ≤ WassFSG.Lip.empMean z f
          + rhoN ħ τ t RG rstar n * gradNorm Ptrue f
          + 4 * rstar + 2 * epsN ħ τ t RG n)}
      ≤ ENNReal.ofReal ((WassFSG.Lip.peelCount γ₂ τ t n : ℝ) * Real.exp (-t)) := by sorry

end WassFSG.Grad

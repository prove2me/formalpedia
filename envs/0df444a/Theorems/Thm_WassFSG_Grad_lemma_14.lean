-- Prove2me | Theorems.Thm_WassFSG_Grad_lemma_14
-- name    : WassFSG.Grad.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:29:17.110253+00:00
-- url     : https://prove2.me/theorems/4981f3da-fcaf-4d79-8b23-972945571f9e
-- title:
--   Lemma 14 — peeling, E_{P_true}f ≤ E_{P_n}f + 2√(τt/n)(1 + E_⊗[𝔑_n(G)])‖‖∇f‖_*‖_{P_true,2} + 2E_⊗[𝔑_n(F)] + ε_n
-- statement:
--   Let $\mathbb P_{\mathrm{true}}$ satisfy $T_2(\tau)$ on a separable Banach space $\mathcal Z$, let $\mathcal F$ satisfy Assumption 2 with constant $\hbar>0$, and assume $0<\|\|\nabla f\|_*\|_{\mathbb P_{\mathrm{true}},2}\le\gamma_2$ for every $f\in\mathcal F$, for some $\gamma_2>0$. Let $t>0$, $n\ge1$, and suppose $\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]$ is finite. Set
--   $$
--   N_2=\max\big(0,\lceil\log_2(\gamma_2\sqrt{\tau t n})\rceil\big)+1 .
--   $$
--   Then with probability at least $1-N_2e^{-t}$, for every $f\in\mathcal F$,
--   $$
--   \mathbb E_{\mathbb P_{\mathrm{true}}}[f]\le\mathbb E_{\mathbb P_n}[f]+2\sqrt{\frac{\tau t}{n}}\big(1+\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]\big)\|\|\nabla f\|_*\|_{\mathbb P_{\mathrm{true}},2}+2\,\mathbb E_\otimes[\mathfrak R_n(\mathcal F)]+\frac{\hbar\tau t+1+\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]}{n}.
--   $$
--
--   The bound is now in terms of each loss's own gradient norm instead of the class supremum; it is the step that makes Theorem 3 adaptive.
--
--   **Formalization Note** The page's failure probability is $\lceil\log_2(\gamma_2\sqrt{\tau tn})\rceil e^{-t}$. That count is $\le0$ when $\gamma_2\sqrt{\tau tn}\le1$ (the claim would then assert probability at least $1$ or more), and the proof's peeling classes $\mathcal F_1,\dots,\mathcal F_{K-1},\mathcal F_K$ miss the band $2^{-K}r<\|\|\nabla f\|_*\|\le2^{-K+1}r$. The corrected count $N_2$ (shells $k=1,\dots,K_0$ with $K_0=\max(0,\lceil\log_2(\gamma_2\sqrt{\tau tn})\rceil)$ plus a bottom class) repairs both. The bound $\gamma_2$ is not restated in the printed lemma, whose proof begins "Set $r=\sup_f\|\|\nabla f\|_*\|_{\mathbb P_{\mathrm{true}},2}\le\gamma_2$"; it is added as a hypothesis. Positivity of the gradient norms makes $\mathcal G$ defined; $\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]$ enters as a real number $R_{\mathcal G}$.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 14, p. 30

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Grad_Setting
import Definitions.Def_WassFSG_Grad_Rademacher

open MeasureTheory

namespace WassFSG.Grad

theorem lemma_14 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : IsT2 τ Ptrue)
    (F : Set (Z → ℝ)) (ħ : ℝ) (hF : GradLipBound ħ F)
    (hpos : ∀ f ∈ F, 0 < gradNorm Ptrue f)
    (γ₂ : ℝ) (hγ₂ : 0 < γ₂) (hbound : ∀ f ∈ F, gradNorm Ptrue f ≤ γ₂)
    (t : ℝ) (ht : 0 < t) (n : ℕ) (hn : 0 < n)
    (RG : ℝ) (hRG : WassFSG.Lip.expectedRad Ptrue n (gradClass Ptrue F) = (RG : EReal)) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
          ((WassFSG.Lip.empMean z f + 2 * Real.sqrt (τ * t / n) * (1 + RG) * gradNorm Ptrue f : ℝ) : EReal)
            + 2 * WassFSG.Lip.expectedRad Ptrue n F + (((ħ * τ * t + 1 + RG) / n : ℝ) : EReal))}
      ≤ ENNReal.ofReal ((WassFSG.Lip.peelCount γ₂ τ t n : ℝ) * Real.exp (-t)) := by sorry

end WassFSG.Grad

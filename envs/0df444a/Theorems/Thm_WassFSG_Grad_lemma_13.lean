-- Prove2me | Theorems.Thm_WassFSG_Grad_lemma_13
-- name    : WassFSG.Grad.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:29:06.161998+00:00
-- url     : https://prove2.me/theorems/383d7c69-e398-4437-af87-8b12b95dfcc6
-- title:
--   Lemma 13 — under T₂(τ), w.p. ≥ 1 − e^{−t}, E_{P_true}f ≤ E_{P_n}f + √(τt/n)(1 + E_⊗[𝔑_n(G)]) sup_F ‖‖∇f‖_*‖_{P_true,2} + 2E_⊗[𝔑_n(F)] + ħτt/n
-- statement:
--   Let $\mathbb P_{\mathrm{true}}$ satisfy $T_2(\tau)$ on a separable Banach space $\mathcal Z$, let $\mathcal F$ satisfy Assumption 2 with constant $\hbar>0$, and assume $\|\|\nabla f\|_*\|_{\mathbb P_{\mathrm{true}},2}>0$ for every $f\in\mathcal F$, so that the normalized gradient class $\mathcal G$ is defined. Let $t>0$, $n\ge1$, and suppose $\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]$ is finite. Then with probability at least $1-e^{-t}$, for every $f\in\mathcal F$,
--   $$
--   \mathbb E_{\mathbb P_{\mathrm{true}}}[f]\le\mathbb E_{\mathbb P_n}[f]+\sqrt{\frac{\tau t}{n}}\big(1+\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]\big)\sup_{f\in\mathcal F}\|\|\nabla f\|_*\|_{\mathbb P_{\mathrm{true}},2}+2\,\mathbb E_\otimes[\mathfrak R_n(\mathcal F)]+\frac{\hbar\tau t}{n}.
--   $$
--
--   This is the $p=2$ counterpart of the Lipschitz bound: the transport term of Lemma 9 is replaced by a gradient-norm term, at the cost of the curvature remainder $\hbar\tau t/n$.
--
--   **Formalization Note** The supremum of gradient norms is taken in the extended reals (it may be $+\infty$, in which case the bound is vacuous; a real supremum would wrongly be $0$). $\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]$ enters as a real number $R_{\mathcal G}$ with a hypothesis equating it to the expectation; when that expectation is $+\infty$ the bound is vacuous anyway. Positivity of the gradient norms is the implicit reading that makes $\mathcal G$ defined. The probability statement is an outer-measure bound on the set of bad samples, with "for every $f$" inside the event. The paper's printed proof (p. 30) uses an inequality $\mathbb E_\sigma\sup_f c_fa_f\le\sup_f c_f\,\mathbb E_\sigma\sup_f a_f$ that does not hold in general for signed $a_f$; the statement itself is posed as printed.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 13, p. 29 (proof pp. 29–30)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Grad_Setting
import Definitions.Def_WassFSG_Grad_Rademacher

open MeasureTheory

namespace WassFSG.Grad

theorem lemma_13 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : IsT2 τ Ptrue)
    (F : Set (Z → ℝ)) (ħ : ℝ) (hF : GradLipBound ħ F)
    (hpos : ∀ f ∈ F, 0 < gradNorm Ptrue f) (t : ℝ) (ht : 0 < t) (n : ℕ) (hn : 0 < n)
    (RG : ℝ) (hRG : WassFSG.Lip.expectedRad Ptrue n (gradClass Ptrue F) = (RG : EReal)) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
          (WassFSG.Lip.empMean z f : EReal)
            + ((Real.sqrt (τ * t / n) * (1 + RG) : ℝ) : EReal)
                * (⨆ g ∈ F, (gradNorm Ptrue g : EReal))
            + 2 * WassFSG.Lip.expectedRad Ptrue n F + ((ħ * τ * t / n : ℝ) : EReal))}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end WassFSG.Grad

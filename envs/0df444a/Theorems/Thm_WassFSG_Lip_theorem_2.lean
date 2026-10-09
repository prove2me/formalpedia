-- Prove2me | Theorems.Thm_WassFSG_Lip_theorem_2
-- name    : WassFSG.Lip.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:39:51.403588+00:00
-- url     : https://prove2.me/theorems/85ae6f28-8d4b-4302-a003-19f6e0a2f192
-- title:
--   Theorem 2 (corrected count) — w.p. ≥ 1 − N₁e^{−t}, E_{P_true}f ≤ E_{P_n}f + (2√(τt/n) + √(4r⋆+2/n))‖f‖_Lip + 4r⋆ + 2/n
-- statement:
--   Let $\mathcal Z$ be a separable Banach space and let $\mathbb P_{\mathrm{true}}$ satisfy $T_1(\tau)$. Let $\mathcal F$ satisfy Assumption 1(I) with constant $\gamma_1>0$, and let $n\ge1$. Assume Assumption 5 with $T(f) = \|f\|^2_{\mathrm{Lip}}$: $\psi_n$ is a sub-root function with
--   $$
--   \psi_n(r)\ge\mathbb E_\otimes\Big[\mathfrak R_n\big(\{cf : f\in\mathcal F,\ 0\le c\le1,\ \|cf\|^2_{\mathrm{Lip}}\le r\}\big)\Big]\qquad(r\ge0),
--   $$
--   and $r_{n\star} > 0$ is its fixed point, $\psi_n(r_{n\star}) = r_{n\star}$. Let $t>0$ and $N_1(t,n) = \max(0,\lceil\log_2(\gamma_1\sqrt{\tau tn})\rceil)+1$. Then with probability at least $1 - N_1(t,n)\,e^{-t}$,
--   $$
--   \mathbb E_{\mathbb P_{\mathrm{true}}}[f] \le \mathbb E_{\mathbb P_n}[f] + \Big(2\sqrt{\frac{\tau t}{n}} + \sqrt{4r_{n\star} + \frac2n}\Big)\|f\|_{\mathrm{Lip}} + 4r_{n\star} + \frac2n \qquad\forall f\in\mathcal F.
--   $$
--
--   This is the paper's Lipschitz-regularization generalization bound: the true loss of every $f$ is bounded by its empirical loss plus a Lipschitz penalty with coefficient of order $\sqrt{1/n}$ (when $r_{n\star} = \tilde O(1/n)$) plus an $O(r_{n\star} + 1/n)$ remainder.
--
--   **Formalization Note** The page prints the failure probability as $\lceil\log_2(\sqrt{\gamma_1\tau tn})\rceil e^{-t}$; that count can be negative and does not match the peeling in the proof of Lemma 12 (see the note of Lemma 12). The Lean states $1 - N_1(t,n)e^{-t}$: the proof applies Lemma 12 to the rescaled class $\{\tfrac{\sqrt{r_0}}{\sqrt{r_0}\vee\|f\|_{\mathrm{Lip}}}f\}$, which satisfies Assumption 1(I) with the same $\gamma_1$. $r_{n\star}$ is the positive fixed point (taking $0$ when $\psi_n(0)=0$ would trivialize the bound). The uniform event is an outer-measure bound on the bad set. Standing conventions: $\mathcal Z$ is a separable real Banach space with its Borel $\sigma$-algebra; $n\ge1$; $\mathbb E_{\mathbb P_{\mathrm{true}}}[f]$ is the Bochner integral (finite for Lipschitz $f$ under $\mathbb P_{\mathrm{true}}\in\mathcal P_1$).
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Theorem 2, p. 10; proof pp. 27–28 (failure probability corrected)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting
import Definitions.Def_WassFSG_Lip_Rademacher

open MeasureTheory

namespace WassFSG.Lip

theorem theorem_2 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : IsT1 τ Ptrue)
    (F : Set (Z → ℝ)) (γ₁ : ℝ) (hF : LipBound γ₁ F) (n : ℕ) (hn : 0 < n)
    (ψ : ℝ → ℝ) (h5 : SubRootLocalComplexity Ptrue n F ψ)
    (rstar : ℝ) (hrstar : 0 < rstar) (hfix : ψ rstar = rstar) (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (∫ x, f x ∂Ptrue ≤ empMean z f
          + (2 * Real.sqrt (τ * t / n) + Real.sqrt (4 * rstar + 2 / n)) * WassFSG.Conc.lipNorm f
          + 4 * rstar + 2 / n)}
      ≤ ENNReal.ofReal ((peelCount γ₁ τ t n : ℝ) * Real.exp (-t)) := by sorry

end WassFSG.Lip

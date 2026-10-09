-- Prove2me | Theorems.Thm_WassFSG_Lip_lemma_12
-- name    : WassFSG.Lip.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:39:42.524275+00:00
-- url     : https://prove2.me/theorems/e8aceac1-d923-4173-bbee-6c2c90f54552
-- title:
--   Lemma 12 (corrected count) — w.p. ≥ 1 − N₁e^{−t}, E_{P_true}f ≤ E_{P_n}f + 2√(τt/n)‖f‖_Lip + 2E_⊗[𝔑_n(F)] + 1/n
-- statement:
--   Let $\mathbb P_{\mathrm{true}}$ satisfy $T_1(\tau)$, and let $\mathcal F$ satisfy Assumption 1(I) with constant $\gamma_1>0$. Let $t>0$, $n\ge1$, and
--   $$
--   N_1(t,n) = \max\big(0, \lceil\log_2(\gamma_1\sqrt{\tau t n})\rceil\big) + 1.
--   $$
--   Then with probability at least $1 - N_1(t,n)\,e^{-t}$,
--   $$
--   \mathbb E_{\mathbb P_{\mathrm{true}}}[f] \le \mathbb E_{\mathbb P_n}[f] + 2\sqrt{\frac{\tau t}{n}}\,\|f\|_{\mathrm{Lip}} + 2\,\mathbb E_\otimes[\mathfrak R_n(\mathcal F)] + \frac1n \qquad \forall f\in\mathcal F.
--   $$
--
--   The bound replaces the class-wide Lipschitz norm of Lemma 11 by each function's own Lipschitz norm, at the price of a logarithmic number of events and an additive $1/n$.
--
--   **Formalization Note** The page prints the failure probability as $\lceil\log_2(\sqrt{\gamma_1\tau t n})\rceil e^{-t}$. That count is wrong in three ways: (a) for $\gamma_1\sqrt{\tau tn}\le 1/2$ it is $\le -1$ (e.g. $\tau = t = n = 1$, $\gamma_1 = 1/4$ gives $\lceil\log_2(1/2)\rceil = -1$), so the claim reads "probability at least $1 + e^{-t}$", false for every event; (b) the proof sets $K = \lceil\log_2(\gamma_1\sqrt{\tau t n})\rceil$, with $\gamma_1$ outside the root, which is what makes $\sqrt{\tau t/n}\,2^{-K}\gamma_1\le 1/n$; (c) the proof's classes miss the band $2^{-K}r < \|f\|_{\mathrm{Lip}}\le 2^{-K+1}r$. Peeling with $K_0 = \max(0,\lceil\log_2(\gamma_1\sqrt{\tau tn})\rceil)$ shells plus a bottom class uses $K_0 + 1 = N_1$ events and leaves the residual $\le 1/n$; the Lean states this corrected count. The uniform event is an outer-measure bound on the bad set. Standing conventions as in Lemma 11.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 12 and its proof, p. 27 (failure probability corrected)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting
import Definitions.Def_WassFSG_Lip_Rademacher

open MeasureTheory

namespace WassFSG.Lip

theorem lemma_12 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : IsT1 τ Ptrue)
    (F : Set (Z → ℝ)) (γ₁ : ℝ) (hF : LipBound γ₁ F) (t : ℝ) (ht : 0 < t) (n : ℕ) (hn : 0 < n) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
          ((empMean z f + 2 * Real.sqrt (τ * t / n) * WassFSG.Conc.lipNorm f : ℝ) : EReal)
            + 2 * expectedRad Ptrue n F + ((1 / (n : ℝ) : ℝ) : EReal))}
      ≤ ENNReal.ofReal ((peelCount γ₁ τ t n : ℝ) * Real.exp (-t)) := by sorry

end WassFSG.Lip

-- Prove2me | Theorems.Thm_WassFSG_Lip_corollary_4
-- name    : WassFSG.Lip.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:39:49.616176+00:00
-- url     : https://prove2.me/theorems/fc78ca9b-1d17-45ae-b9d3-ac42df4bf7aa
-- title:
--   Corollary 4 (corrected count) — under T₁(τ), w.p. ≥ 1 − N₁e^{−t}, E_{P_true}f ≤ E_{P_n}f + R_{P_n,1}(ρ_n; f) + 4r⋆ + 2/n
-- statement:
--   Let $\mathcal Z$ be a separable Banach space and let $\mathbb P_{\mathrm{true}}$ satisfy the transportation-information inequality $T_1(\tau)$. Let $\mathcal F$ be a class of losses satisfying Assumption 1 (both (I), with constant $\gamma_1 > 0$, and (II)), let $n\ge1$, and assume Assumption 5 with $T(f) = \|f\|^2_{\mathrm{Lip}}$: a sub-root function $\psi_n$ dominates the localized Rademacher complexities,
--   $$
--   \psi_n(r)\ge\mathbb E_\otimes\Big[\mathfrak R_n\big(\{cf : f\in\mathcal F,\ 0\le c\le 1,\ \|cf\|^2_{\mathrm{Lip}}\le r\}\big)\Big]\qquad (r\ge0),
--   $$
--   with positive fixed point $r_{n\star} = \psi_n(r_{n\star}) > 0$. Let $t > 0$ and set
--   $$
--   \rho_n = 2\sqrt{\frac{\tau t}{n}} + \sqrt{4r_{n\star} + \frac2n}, \qquad N_1(t,n) = \max\big(0,\lceil\log_2(\gamma_1\sqrt{\tau tn})\rceil\big) + 1.
--   $$
--   Then, for an i.i.d. sample $z_1,\dots,z_n$ from $\mathbb P_{\mathrm{true}}$ with empirical distribution $\mathbb P_n$, with probability at least $1 - N_1(t,n)\,e^{-t}$,
--   $$
--   \mathbb E_{\mathbb P_{\mathrm{true}}}[f] \le \mathbb E_{\mathbb P_n}[f] + \mathcal R_{\mathbb P_n,1}(\rho_n; f) + 4r_{n\star} + \frac2n\qquad\forall f\in\mathcal F,
--   $$
--   where $\mathcal R_{\mathbb P_n,1}(\rho_n;f) = \sup\{\mathbb E_{\mathbb P}[f] : \mathbb P\in\mathcal P_1(\mathcal Z),\ \mathcal W_1(\mathbb P,\mathbb P_n)\le\rho_n\} - \mathbb E_{\mathbb P_n}[f]$. Equivalently, the 1-Wasserstein robust loss at radius $\rho_n$ around $\mathbb P_n$ bounds the true loss of every $f$ up to $4r_{n\star} + 2/n$.
--
--   This is the paper's finite-sample guarantee for 1-Wasserstein DRO: the radius $\rho_n$ is of order $1/\sqrt n$ whenever $r_{n\star} = \tilde O(1/n)$, with no dependence on the dimension of $\mathcal Z$.
--
--   **Formalization Note** The printed failure probability $\lceil\log_2(\sqrt{\gamma_1\tau tn})\rceil e^{-t}$ is corrected to $N_1(t,n)e^{-t}$ (the printed count can be negative, which makes the printed claim false; see Lemma 12). "With probability at least $1-\delta$, for every $f$" is the outer-measure bound $\mathbb P_\otimes\{z : \exists f\in\mathcal F$ violating the inequality$\}\le\delta$, and $\mathcal R_{\mathbb P_n,1}$ is computed at the empirical distribution of the same sample $z$. $r_{n\star}$ is the positive fixed point of $\psi_n$. The comparison is in the extended reals; $\mathbb E_{\mathbb P_{\mathrm{true}}}[f]$ is the Bochner integral (finite for Lipschitz $f$ under $\mathbb P_{\mathrm{true}}\in\mathcal P_1$). Standing conventions: $\mathcal Z$ is a separable real Banach space with its Borel $\sigma$-algebra (the page says "Banach space"); $n\ge1$.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Corollary 4, p. 10 (failure probability corrected)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting
import Definitions.Def_WassFSG_Lip_Rademacher

open MeasureTheory

namespace WassFSG.Lip

theorem corollary_4 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : IsT1 τ Ptrue)
    (F : Set (Z → ℝ)) (γ₁ : ℝ) (hF : LipBound γ₁ F) (hF2 : LipAttainedAtInfinity F)
    (n : ℕ) (hn : 0 < n)
    (ψ : ℝ → ℝ) (h5 : SubRootLocalComplexity Ptrue n F ψ)
    (rstar : ℝ) (hrstar : 0 < rstar) (hfix : ψ rstar = rstar) (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
          (empMean z f : EReal)
            + regularizer (empMeasure z)
                (2 * Real.sqrt (τ * t / n) + Real.sqrt (4 * rstar + 2 / n)) f
            + ((4 * rstar + 2 / n : ℝ) : EReal))}
      ≤ ENNReal.ofReal ((peelCount γ₁ τ t n : ℝ) * Real.exp (-t)) := by sorry

end WassFSG.Lip

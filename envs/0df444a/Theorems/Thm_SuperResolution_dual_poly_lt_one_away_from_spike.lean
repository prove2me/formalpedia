-- Prove2me | Theorems.Thm_SuperResolution_dual_poly_lt_one_away_from_spike
-- name    : SuperResolution.dual_poly_lt_one_away_from_spike
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:13:16.238493+00:00
-- url     : https://prove2.me/theorems/244aaf30-8943-4faa-828a-8e7230ec72fd
-- title:
--   Lemma 2.4: the dual polynomial is below one between spikes
-- statement:
--   Under the hypotheses of Lemma 2.3 ($f_c\ge128$ even, $T\subset[0,1)$ with $\Delta(T)\ge2\lambda_c$, $|v_t|=1$, and $\alpha,\beta$ solving $q(t_k)=v_k$, $q'(t_k)=0$), fix $\tau\in T$.
--
--   1. $|q(t)|<1$ whenever $0.1649\,\lambda_c\le|t-\tau|\le\Delta(T)/2$.
--   2. Let $\tau_+$ be the closest spike to the right of $\tau$. Then $|q(t)|<1$ for all $t$ with $0<t-\tau\le(\tau_+-\tau)/2$, and likewise on the left side of $\tau$.
--
--   **Formalization Note** Distances are wrap-around distances. The condition $t-\tau\le(\tau_+-\tau)/2$ for $t=\tau+s$ is written as: no point of $T$ lies in the open arc from $\tau$ to $\tau+2s$. This also covers a single spike, where $\tau_+$ is $\tau$ itself one turn later. The coefficients and the evenness of $f_c$ are handled as in Lemma 2.3.
-- source:
--   Candès and Fernandez-Granda, Towards a Mathematical Theory of Super-Resolution, arXiv:1203.5871v3 (2012), Section 2.2, Lemma 2.4, eq. (2.4), p. 16; proof in Section 2.3.3, pp. 23–24

import Mathlib
import Definitions.Def_SuperResolution_Basic

open MeasureTheory

namespace SuperResolution

theorem dual_poly_lt_one_away_from_spike (fc : ℕ) (hfc : 128 ≤ fc) (hev : Even fc)
    (T : Finset ℝ) (hT : ∀ t ∈ T, 0 ≤ t ∧ t < 1)
    (hsep : ENNReal.ofReal (2 / fc) ≤ minSep (circlePts T))
    (v : ℝ → ℂ) (hv : ∀ t ∈ T, ‖v t‖ = 1) (α β : ℝ → ℂ) (hαβ : IsInterpCoeff fc T v α β)
    (τ : ℝ) (hτ : τ ∈ T) :
    (∀ t : ℝ, 0.1649 / fc ≤ dist (t : UnitAddCircle) (τ : UnitAddCircle) →
      ENNReal.ofReal (2 * dist (t : UnitAddCircle) (τ : UnitAddCircle)) ≤ minSep (circlePts T) →
      ‖dualPoly fc T α β t‖ < 1) ∧
    (∀ s : ℝ, 0 < s →
      (∀ s' ∈ Set.Ioo 0 (2 * s), ((τ + s' : ℝ) : UnitAddCircle) ∉ circlePts T) →
      ‖dualPoly fc T α β (τ + s)‖ < 1) ∧
    (∀ s : ℝ, 0 < s →
      (∀ s' ∈ Set.Ioo 0 (2 * s), ((τ - s' : ℝ) : UnitAddCircle) ∉ circlePts T) →
      ‖dualPoly fc T α β (τ - s)‖ < 1) := by sorry

end SuperResolution

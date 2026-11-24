-- Prove2me | Theorems.Thm_SuperResolution_dual_poly_quadratic_decay
-- name    : SuperResolution.dual_poly_quadratic_decay
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:15:34.932589+00:00
-- url     : https://prove2.me/theorems/ed247ba2-24c7-4e7a-afd2-e8565bb5a781
-- title:
--   Lemma 2.5: quadratic decay of the dual polynomial at separation 2.5
-- statement:
--   Let $f_c\ge128$ be even, let $T\subset[0,1)$ be finite with $\Delta(T)\ge2.5\,\lambda_c$, let $|v_t|=1$ for $t\in T$, and let $\alpha,\beta$ solve $q(t_k)=v_k$, $q'(t_k)=0$ on $T$, where $q=\sum_{t_j\in T}\alpha_jK(\cdot-t_j)+\beta_jK'(\cdot-t_j)$. Then for every $\tau\in T$,
--
--   $$|q(t)|\le1-0.3353\,f_c^2\,(t-\tau)^2\qquad\text{for all }t\text{ with }|t-\tau|\le0.1649\,\lambda_c,$$
--
--   and if $\min_{\tau\in T}|t-\tau|>0.1649\,\lambda_c$, then $|q(t)|\le1-0.3353\,f_c^2\,(0.1649\,\lambda_c)^2$.
--
--   This quantitative margin feeds the null-space property of Lemma 3.1.
--
--   **Formalization Note** $|t-\tau|$ is the wrap-around distance and $(t-\tau)^2$ is its square. The hypotheses $f_c\ge128$ and even $f_c$ are those of the construction in Section 2, which the lemma refers to.
-- source:
--   Candès and Fernandez-Granda, Towards a Mathematical Theory of Super-Resolution, arXiv:1203.5871v3 (2012), Section 2.2, Lemma 2.5, eq. (2.9), p. 16; proof in Section 2.4, pp. 24–25

import Mathlib
import Definitions.Def_SuperResolution_Basic

open MeasureTheory

namespace SuperResolution

theorem dual_poly_quadratic_decay (fc : ℕ) (hfc : 128 ≤ fc) (hev : Even fc)
    (T : Finset ℝ) (hT : ∀ t ∈ T, 0 ≤ t ∧ t < 1)
    (hsep : ENNReal.ofReal (2.5 / fc) ≤ minSep (circlePts T))
    (v : ℝ → ℂ) (hv : ∀ t ∈ T, ‖v t‖ = 1) (α β : ℝ → ℂ) (hαβ : IsInterpCoeff fc T v α β) :
    (∀ τ ∈ T, ∀ t : ℝ, dist (t : UnitAddCircle) (τ : UnitAddCircle) ≤ 0.1649 / fc →
      ‖dualPoly fc T α β t‖ ≤ 1 - 0.3353 * (fc : ℝ) ^ 2 * dist (t : UnitAddCircle) (τ : UnitAddCircle) ^ 2) ∧
    (∀ t : ℝ, (∀ τ ∈ T, 0.1649 / fc < dist (t : UnitAddCircle) (τ : UnitAddCircle)) →
      ‖dualPoly fc T α β t‖ ≤ 1 - 0.3353 * (fc : ℝ) ^ 2 * (0.1649 / fc) ^ 2) := by sorry

end SuperResolution

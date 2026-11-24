-- Prove2me | Theorems.Thm_SuperResolution_dual_poly_lt_one_near_spike
-- name    : SuperResolution.dual_poly_lt_one_near_spike
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:12:49.191996+00:00
-- url     : https://prove2.me/theorems/d8c455ab-c9a3-49d5-a830-e50e389405eb
-- title:
--   Lemma 2.3: the dual polynomial is below one near each spike
-- statement:
--   Let $f_c\ge128$ be even, let $T\subset[0,1)$ be finite with $\Delta(T)\ge2\lambda_c$, let $|v_t|=1$ for $t\in T$, and let $\alpha,\beta$ be coefficients with $q(t_k)=v_k$ and $q'(t_k)=0$ for all $t_k\in T$, where $q(t)=\sum_{t_j\in T}\alpha_jK(t-t_j)+\beta_jK'(t-t_j)$. Fix $\tau\in T$. Then
--
--   $$|q(t)|<1\qquad\text{whenever }0<|t-\tau|\le0.1649\,\lambda_c,$$
--
--   where $|t-\tau|$ is the wrap-around distance.
--
--   **Formalization Note** The paper's $q$ uses the coefficients of Lemma 2.2. The statement is made for every pair $(\alpha,\beta)$ solving the interpolation equations, which the proof of Lemma 2.2 shows is the unique solution. Evenness of $f_c$ is added as in Lemma 2.2.
-- source:
--   Candès and Fernandez-Granda, Towards a Mathematical Theory of Super-Resolution, arXiv:1203.5871v3 (2012), Section 2.2, Lemma 2.3, eq. (2.4), p. 16; proof in Section 2.3.2, pp. 21–23

import Mathlib
import Definitions.Def_SuperResolution_Basic

open MeasureTheory

namespace SuperResolution

theorem dual_poly_lt_one_near_spike (fc : ℕ) (hfc : 128 ≤ fc) (hev : Even fc)
    (T : Finset ℝ) (hT : ∀ t ∈ T, 0 ≤ t ∧ t < 1)
    (hsep : ENNReal.ofReal (2 / fc) ≤ minSep (circlePts T))
    (v : ℝ → ℂ) (hv : ∀ t ∈ T, ‖v t‖ = 1) (α β : ℝ → ℂ) (hαβ : IsInterpCoeff fc T v α β)
    (τ : ℝ) (hτ : τ ∈ T) (t : ℝ)
    (h0 : 0 < dist (t : UnitAddCircle) (τ : UnitAddCircle))
    (h1 : dist (t : UnitAddCircle) (τ : UnitAddCircle) ≤ 0.1649 / fc) :
    ‖dualPoly fc T α β t‖ < 1 := by sorry

end SuperResolution

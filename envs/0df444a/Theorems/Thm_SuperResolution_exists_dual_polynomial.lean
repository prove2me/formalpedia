-- Prove2me | Theorems.Thm_SuperResolution_exists_dual_polynomial
-- name    : SuperResolution.exists_dual_polynomial
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:13:58.877984+00:00
-- url     : https://prove2.me/theorems/c54ce103-42fe-421d-a0f8-9308cf7f34b8
-- title:
--   Proposition 2.1: existence of a dual polynomial under the separation condition
-- statement:
--   Let $f_c\ge128$ and let $T\subset\mathbb{T}$ be finite with minimum (wrap-around) separation
--
--   $$\Delta(T)\ge\frac{2}{f_c}=2\lambda_c.$$
--
--   Then for every $v\in\mathbb{C}^{|T|}$ with $|v_t|=1$ there is a low-frequency trigonometric polynomial $q(t)=\sum_{k=-f_c}^{f_c}c_ke^{i2\pi kt}$ with $q(t)=v_t$ for $t\in T$ and $|q(t)|<1$ for $t\in\mathbb{T}\setminus T$.
--
--   Together with Proposition A.1 this gives Theorem 1.2.
-- source:
--   Candès and Fernandez-Granda, Towards a Mathematical Theory of Super-Resolution, arXiv:1203.5871v3 (2012), Section 2.2, Proposition 2.1, eqs. (1.6), (2.1), (2.2), p. 15

import Mathlib
import Definitions.Def_SuperResolution_Basic

open MeasureTheory

namespace SuperResolution

theorem exists_dual_polynomial (fc : ℕ) (hfc : 128 ≤ fc) (T : Finset UnitAddCircle)
    (hsep : ENNReal.ofReal (2 / fc) ≤ minSep T)
    (v : UnitAddCircle → ℂ) (hv : ∀ t ∈ T, ‖v t‖ = 1) :
    ∃ c : ℤ → ℂ, (∀ t ∈ T, trigPoly fc c t = v t) ∧ ∀ t, t ∉ T → ‖trigPoly fc c t‖ < 1 := by sorry

end SuperResolution

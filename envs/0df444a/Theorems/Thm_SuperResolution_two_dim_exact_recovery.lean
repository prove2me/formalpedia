-- Prove2me | Theorems.Thm_SuperResolution_two_dim_exact_recovery
-- name    : SuperResolution.two_dim_exact_recovery
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:17:52.228033+00:00
-- url     : https://prove2.me/theorems/2c16206c-c26c-484c-bee2-cad33a5d2060
-- title:
--   Theorem 1.3 (as proved): exact recovery of separated real spikes in two dimensions
-- statement:
--   Let $f_c\ge512$, let $T\subset\mathbb{T}^2$ be finite with minimum separation
--
--   $$\Delta(T)\ge\frac{2.38}{f_c}=2.38\,\lambda_c$$
--
--   in the wrap-around $\ell_\infty$ distance, and let $x=\sum_{t\in T}a_t\delta_t$ with real $a_t\ne0$. Then $x$ is the unique minimum total-variation solution, among all real measures $\tilde x$ on $\mathbb{T}^2$, of the constraints $\int e^{-i2\pi\langle k,t\rangle}\tilde x(\mathrm{d}t)=\int e^{-i2\pi\langle k,t\rangle}x(\mathrm{d}t)$ for $k\in\mathbb{Z}^2$, $|k_1|,|k_2|\le f_c$.
--
--   **Formalization Note** Theorem 1.3 as printed does not state a lower bound on $f_c$. Its proof (Proposition C.1) assumes $f_c\ge512$, which is added. The printed sentence on complex measures ("a slightly different constant") gives no constant and is not included.
-- source:
--   Candès and Fernandez-Granda, Towards a Mathematical Theory of Super-Resolution, arXiv:1203.5871v3 (2012), Section 1.3, Theorem 1.3, eqs. (1.7)–(1.8), p. 6; proof in Appendix C (Proposition C.1, $f_c \ge 512$), p. 41

import Mathlib
import Definitions.Def_SuperResolution_Basic

open MeasureTheory

namespace SuperResolution

theorem two_dim_exact_recovery (fc : ℕ) (hfc : 512 ≤ fc)
    (T : Finset (UnitAddCircle × UnitAddCircle)) (a : UnitAddCircle × UnitAddCircle → ℂ)
    (ha : ∀ t ∈ T, a t ≠ 0) (hreal : ∀ t ∈ T, (a t).im = 0)
    (hsep : ENNReal.ofReal (2.38 / fc) ≤ minSep T) :
    IsUniqueRealTVSolution2D fc (atomicMeasure T a) := by sorry

end SuperResolution

-- Prove2me | Theorems.Thm_SuperResolution_interpolation_coefficient_bounds
-- name    : SuperResolution.interpolation_coefficient_bounds
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:12:16.244408+00:00
-- url     : https://prove2.me/theorems/a451a6b2-6ab8-480c-bf22-5df992e7d102
-- title:
--   Lemma 2.2: the interpolation coefficients exist and are bounded
-- statement:
--   Let $f_c\ge128$ be even and let $T\subset[0,1)$ be finite with wrap-around minimum separation $\Delta(T)\ge2/f_c=2\lambda_c$. Let $v_t\in\mathbb{C}$ with $|v_t|=1$ for $t\in T$. Then there are coefficient vectors $\alpha,\beta$ indexed by $T$ for which the dual polynomial $q(t)=\sum_{t_j\in T}\alpha_jK(t-t_j)+\beta_jK'(t-t_j)$ obeys
--
--   $$q(t_k)=v_k,\qquad q'(t_k)=0\qquad(t_k\in T),$$
--
--   and
--
--   $$\|\alpha\|_\infty\le1+8.824\cdot10^{-3},\qquad\|\beta\|_\infty\le3.294\cdot10^{-2}\,\lambda_c.$$
--
--   Further, for every $\tau\in T$ with $v_\tau=1$: $\operatorname{Re}\alpha_\tau\ge1-8.824\cdot10^{-3}$ and $|\operatorname{Im}\alpha_\tau|\le8.824\cdot10^{-3}$.
--
--   **Formalization Note** The paper's "if $v_1=1$" refers to an arbitrary labelled spike and is stated for every $\tau\in T$. Evenness of $f_c$ is added: the paper's construction uses that $K$ is a trigonometric polynomial of the form (2.1), which it states only for even $f_c$ (for odd $f_c$ the formula for $K$ is not $1$-periodic).
-- source:
--   Candès and Fernandez-Granda, Towards a Mathematical Theory of Super-Resolution, arXiv:1203.5871v3 (2012), Section 2.2, Lemma 2.2, eqs. (2.3)–(2.8), pp. 15–16; proof in Section 2.3.1, pp. 19–21

import Mathlib
import Definitions.Def_SuperResolution_Basic

open MeasureTheory

namespace SuperResolution

theorem interpolation_coefficient_bounds (fc : ℕ) (hfc : 128 ≤ fc) (hev : Even fc)
    (T : Finset ℝ) (hT : ∀ t ∈ T, 0 ≤ t ∧ t < 1)
    (hsep : ENNReal.ofReal (2 / fc) ≤ minSep (circlePts T))
    (v : ℝ → ℂ) (hv : ∀ t ∈ T, ‖v t‖ = 1) :
    ∃ α β : ℝ → ℂ, IsInterpCoeff fc T v α β ∧
      (∀ t ∈ T, ‖α t‖ ≤ 1 + 8.824e-3) ∧ (∀ t ∈ T, ‖β t‖ ≤ 3.294e-2 / fc) ∧
      (∀ τ ∈ T, v τ = 1 → 1 - 8.824e-3 ≤ (α τ).re ∧ |(α τ).im| ≤ 8.824e-3) := by sorry

end SuperResolution

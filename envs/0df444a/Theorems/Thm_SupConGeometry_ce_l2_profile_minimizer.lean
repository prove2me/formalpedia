-- Prove2me | Theorems.Thm_SupConGeometry_ce_l2_profile_minimizer
-- name    : SupConGeometry.ce_l2_profile_minimizer
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:14:39.737929+00:00
-- url     : https://prove2.me/theorems/344f06e3-1fc8-4d9d-9074-3131919275b2
-- title:
--   Lemma 14: the one-dimensional profile is uniquely minimized at $r_{\mathcal W}(\rho_{\mathcal Z},\lambda)>0$
-- statement:
--   Let $K\ge2$ and $\rho,\lambda>0$, and let
--
--   $$f(x)=\log\Big(1+(K-1)\exp\Big(-\rho\frac{K}{K-1}x\Big)\Big)+\lambda Kx^2,\qquad x\in\mathbb R.$$
--
--   The equation
--
--   $$2\lambda x-\frac{\rho}{\exp\big(\frac{K\rho x}{K-1}\big)+K-1}=0$$
--
--   has exactly one real solution $r_{\mathcal W}(\rho,\lambda)$. This solution is positive, and it is the unique minimiser of $f$: $f(r_{\mathcal W})<f(x)$ for every $x\neq r_{\mathcal W}$.
--
--   **Formalization Note** The paper's lemma also lists $h$ and $W\in(\mathbb R^h)^K$, which do not occur in it; they are omitted. The paper writes the equation as $0=K(\cdots)$, which has the same solutions. $r_{\mathcal W}$ is defined as the infimum of the solution set, so this lemma also certifies that the definition picks the solution.
-- source:
--   Graf, Hofer, Niethammer and Kwitt, Dissecting Supervised Contrastive Learning, ICML 2021, arXiv:2102.08817v4, Supplementary S2, Lemma 14, eqs. (147)-(148), p. 34

import Mathlib
import Definitions.Def_SupConGeometry_Basic

open Finset

namespace SupConGeometry

theorem ce_l2_profile_minimizer {K : ℕ} (hK : 2 ≤ K) (ρ lam : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) :
    0 < ceL2Radius K ρ lam ∧
    2 * lam * ceL2Radius K ρ lam -
        ρ / (Real.exp ((K : ℝ) * ρ * ceL2Radius K ρ lam / ((K : ℝ) - 1)) + (K : ℝ) - 1) = 0 ∧
    (∀ x : ℝ, 2 * lam * x - ρ / (Real.exp ((K : ℝ) * ρ * x / ((K : ℝ) - 1)) + (K : ℝ) - 1) = 0 →
      x = ceL2Radius K ρ lam) ∧
    (∀ x : ℝ, x ≠ ceL2Radius K ρ lam →
      ceL2Profile K ρ lam (ceL2Radius K ρ lam) < ceL2Profile K ρ lam x) := by sorry

end SupConGeometry

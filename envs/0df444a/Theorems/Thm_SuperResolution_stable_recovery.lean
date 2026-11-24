-- Prove2me | Theorems.Thm_SuperResolution_stable_recovery
-- name    : SuperResolution.stable_recovery
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:17:25.741287+00:00
-- url     : https://prove2.me/theorems/9842c7a3-7dd6-4287-ab48-4fc7b43613cc
-- title:
--   Theorem 1.5: stable super-resolution with error $O(\mathrm{SRF}^2\delta)$
-- statement:
--   There is a numerical constant $C_0>0$ with the following property. Let $f_c\ge128$, $N\ge n=2f_c+1$, $\mathrm{SRF}=N/n$, and let $x\in\mathbb{C}^N$ have support whose grid points $t/N$ are separated by at least $2\lambda_c$ (wrap-around). Observe
--
--   $$s=P_nx+P_nz,\qquad\|P_nz\|_1\le\delta,$$
--
--   for some $z\in\mathbb{C}^N$, and let $\hat x$ be any solution of $\min\|\tilde x\|_1$ subject to $\|P_n\tilde x-s\|_1\le\delta$. Then
--
--   $$\|\hat x-x\|_1\le C_0\,\mathrm{SRF}^2\,\delta.$$
--
--   The error grows quadratically in the super-resolution factor and linearly in the noise level.
--
--   **Formalization Note** $f_c\ge128$ (from Theorem 1.2) and $N\ge2f_c+1$ (so that $P_n$ is the orthogonal projection the paper describes) are the paper's standing assumptions. $C_0$ is quantified before all data.
-- source:
--   Candès and Fernandez-Granda, Towards a Mathematical Theory of Super-Resolution, arXiv:1203.5871v3 (2012), Section 1.5, Theorem 1.5, eqs. (1.14)–(1.16), p. 9; proof in Section 3.1, p. 26

import Mathlib
import Definitions.Def_SuperResolution_Basic

open MeasureTheory

namespace SuperResolution

theorem stable_recovery :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (N fc : ℕ), 128 ≤ fc → 2 * fc + 1 ≤ N →
      ∀ (x z : Fin N → ℂ) (δ : ℝ),
        ENNReal.ofReal (2 / fc) ≤ minSep ((gridSupport x).image (gridPt N)) →
        l1norm (lowPass N fc z) ≤ δ →
        ∀ xhat : Fin N → ℂ,
          l1norm (lowPass N fc xhat - (lowPass N fc x + lowPass N fc z)) ≤ δ →
          (∀ x' : Fin N → ℂ,
            l1norm (lowPass N fc x' - (lowPass N fc x + lowPass N fc z)) ≤ δ →
            l1norm xhat ≤ l1norm x') →
          l1norm (xhat - x) ≤ C0 * srf N fc ^ 2 * δ := by sorry

end SuperResolution

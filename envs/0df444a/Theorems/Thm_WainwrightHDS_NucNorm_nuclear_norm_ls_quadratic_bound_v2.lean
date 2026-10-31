-- Prove2me | Theorems.Thm_WainwrightHDS_NucNorm_nuclear_norm_ls_quadratic_bound_v2
-- name    : WainwrightHDS.NucNorm.nuclear_norm_ls_quadratic_bound_v2
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T04:12:15.576756+00:00
-- url     : https://prove2.me/theorems/fd1c5eb4-2d53-4449-8587-63235029bc85
-- title:
--   Intermediate quadratic inequality in Proposition 10.6 ($\|{\widehat\Theta}-\Theta^*\|_F^2$)
-- statement:
--   Under restricted strong convexity and the dual-norm bound $\|\frac{1}{n}\sum_{i=1}^n w_i X_i\|_2 \le \lambda_n / 2$, choosing $(U, V)$ to be the top-$r$ singular subspaces of $\Theta^*$ and combining the nuclear-norm cone constraint with $\Psi(\overline{\mathcal{M}}(U, V)) \le \sqrt{2r}$ and $128 c_0 (d_1 + d_2) r \le \kappa n$ yields the quadratic Frobenius error inequality $\kappa \|\widehat{\Theta} - \Theta^*\|_F^2 \le \frac{3}{2} \lambda_n \sqrt{2r} \|\widehat{\Theta} - \Theta^*\|_F + \lambda_n \sum_{j=r}^{\min(d_1,d_2)-1} \sigma_j(\Theta^*) + 16 c_0 \frac{d_1+d_2}{n} (\sum_{j=r}^{\min(d_1,d_2)-1} \sigma_j(\Theta^*))^2$.
-- source:
--   Wainwright, High-Dimensional Statistics (2019), Proposition 10.6, p. 320

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_traceInner
import Definitions.Def_WainwrightHDS_NucNorm_obsOp
import Definitions.Def_WainwrightHDS_NucNorm_frobSq
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_WainwrightHDS_NucNorm_lsNucObjective
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_Mspace
import Definitions.Def_WainwrightHDS_NucNorm_Mbar
import Definitions.Def_WainwrightHDS_NucNorm_MbarPerp
import Definitions.Def_WainwrightHDS_NucNorm_projMat
import Definitions.Def_WainwrightHDS_NucNorm_projM
import Definitions.Def_WainwrightHDS_NucNorm_projMperp
import Definitions.Def_WainwrightHDS_NucNorm_projMbar
import Definitions.Def_WainwrightHDS_NucNorm_projMbarPerp

namespace WainwrightHDS.NucNorm

theorem nuclear_norm_ls_quadratic_bound_v2 {n d₁ d₂ : ℕ}
    (X : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ) (Θstar : Matrix (Fin d₁) (Fin d₂) ℝ)
    (w y : Fin n → ℝ) (hy : ∀ i, y i = obsOp X Θstar i + w i)
    (κ c₀ lam : ℝ) (hκ : 0 < κ) (hc₀ : 0 < c₀) (hlam : 0 < lam)
    (hRSC : ∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ,
      1 / (2 * (n : ℝ)) * ∑ i, (obsOp X Δ i) ^ 2 ≥
        κ / 2 * frobSq Δ - c₀ * (((d₁ : ℝ) + d₂) / n) * nucNorm Δ ^ 2)
    (hG : opNorm2 ((1 / (n : ℝ)) • ∑ i, w i • X i) ≤ lam / 2)
    (Θhat : Matrix (Fin d₁) (Fin d₂) ℝ)
    (hmin : ∀ Θ : Matrix (Fin d₁) (Fin d₂) ℝ, lsNucObjective X y lam Θhat ≤ lsNucObjective X y lam Θ)
    (r : ℕ) (hr₁ : 1 ≤ r) (hrd : r ≤ min d₁ d₂)
    (hrκ : 128 * c₀ * ((d₁ : ℝ) + d₂) * r ≤ κ * n) :
    κ * frobSq (Θhat - Θstar) ≤
      3 / 2 * lam * Real.sqrt (2 * r) * Real.sqrt (frobSq (Θhat - Θstar)) +
        lam * (∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar) +
        16 * c₀ * ((d₁ : ℝ) + d₂) / n *
          (∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar) ^ 2 := by sorry

end WainwrightHDS.NucNorm

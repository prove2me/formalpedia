-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_proposition_3_1_ii
-- name    : SpikedWishart.SoftEdge.proposition_3_1_ii
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T05:53:14.02063+00:00
-- url     : https://prove2.me/theorems/7e64f55d-4792-441f-a667-5c5f67d197d1
-- title:
--   Proposition 3.1 (ii): $|\mathcal J(v)/Z_M-\mathcal J_\infty(v)|\le Ce^{-cv}/M^{1/3}$ uniformly
-- statement:
--   Under the hypotheses of Proposition 3.1 ($\Sigma$ a circle with real centre enclosing $0$ in $\{\mathrm{Re}\,z<q\}$, $\Sigma_\infty$ with vertex in $(-\infty,-\varepsilon)$, the rest as in part (i)): for every $V$ there are $C,c,M_0>0$ with, for $M\ge M_0$ and $v\ge V$,
--
--   $$\Big|\frac1{Z_M}\mathcal J(v)-\mathcal J_\infty(v)\Big|\le\frac{Ce^{-cv}}{M^{1/3}}.$$
--
--   Role: the second half of Proposition 3.1.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, Proposition 3.1 (ii) and its proof, pp. 1660-1664

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex MeasureTheory

namespace SpikedWishart.SoftEdge

theorem proposition_3_1_ii (ε γ₀ c₀ : ℝ) (hε : 0 < ε) (hγ₀ : 1 ≤ γ₀) (hc₀ : 0 < c₀)
    (r k : ℕ) (hkr : k ≤ r) :
    ∀ V₀ : ℝ, ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < M₀ ∧
      ∀ (M N : ℕ) (γ : ℝ) (π : Fin r → ℝ) (cS ρS cJ v : ℝ),
        M₀ ≤ M → r ≤ N → γ = Real.sqrt ((M : ℝ) / (N : ℝ)) → 1 ≤ γ → γ ≤ γ₀ →
        (∀ j : Fin r, (j : ℕ) < k → π j = pc γ) →
        (∀ j : Fin r, k ≤ (j : ℕ) → c₀ ≤ (π j)⁻¹ ∧ (π j)⁻¹ ≤ 1 + γ⁻¹ - c₀) →
        |cS| < ρS → cS + ρS < qM γ ε M →
        cJ < -ε → V₀ ≤ v →
        ‖Jcal γ (qM γ ε M) M k π cS ρS v / ZM γ (qM γ ε M) M k π - Jinf ε k cJ v‖ ≤
          C * Real.exp (-c * v) / (M : ℝ) ^ (1 / 3 : ℝ) := by sorry

end SpikedWishart.SoftEdge

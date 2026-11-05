-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_proposition_3_1_i
-- name    : SpikedWishart.SoftEdge.proposition_3_1_i
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T05:40:28.013261+00:00
-- url     : https://prove2.me/theorems/4cfde12d-d04f-4396-97c3-331c7924515f
-- title:
--   Proposition 3.1 (i): $|Z_M\mathcal H(u)-\mathcal H_\infty(u)|\le Ce^{-cu}/M^{1/3}$ uniformly
-- statement:
--   Under the hypotheses of Proposition 3.1 (fixed $\varepsilon>0$, $\gamma_0\ge1$, $c_0>0$, $0\le k\le r$, $\gamma=\sqrt{M/N}\in[1,\gamma_0]$, spikes $\pi_1=\dots=\pi_k=p_c$ and $c_0\le\pi_j^{-1}\le1+\gamma^{-1}-c_0$ otherwise, $\Gamma$ a circle with real centre enclosing $p_c$, the $\pi_j$ and $1$ in $\{\mathrm{Re}\,z>q\}$, $\Gamma_\infty$ with vertex in $(-\varepsilon,0)$): for every $U$ there are $C,c,M_0>0$ with, for $M\ge M_0$ and $u\ge U$,
--
--   $$\big|Z_M\mathcal H(u)-\mathcal H_\infty(u)\big|\le\frac{Ce^{-cu}}{M^{1/3}}.$$
--
--   Role: the first half of Proposition 3.1.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, Proposition 3.1 (i) and its proof, pp. 1660-1664

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex MeasureTheory

namespace SpikedWishart.SoftEdge

theorem proposition_3_1_i (ε γ₀ c₀ : ℝ) (hε : 0 < ε) (hγ₀ : 1 ≤ γ₀) (hc₀ : 0 < c₀)
    (r k : ℕ) (hkr : k ≤ r) :
    ∀ U₀ : ℝ, ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < M₀ ∧
      ∀ (M N : ℕ) (γ : ℝ) (π : Fin r → ℝ) (cΓ ρΓ cH u : ℝ),
        M₀ ≤ M → r ≤ N → γ = Real.sqrt ((M : ℝ) / (N : ℝ)) → 1 ≤ γ → γ ≤ γ₀ →
        (∀ j : Fin r, (j : ℕ) < k → π j = pc γ) →
        (∀ j : Fin r, k ≤ (j : ℕ) → c₀ ≤ (π j)⁻¹ ∧ (π j)⁻¹ ≤ 1 + γ⁻¹ - c₀) →
        |pc γ - cΓ| < ρΓ → (∀ j, |π j - cΓ| < ρΓ) → |1 - cΓ| < ρΓ → qM γ ε M < cΓ - ρΓ →
        -ε < cH → cH < 0 → U₀ ≤ u →
        ‖ZM γ (qM γ ε M) M k π * Hcal γ (qM γ ε M) M k π cΓ ρΓ u - Hinf ε k cH u‖ ≤
          C * Real.exp (-c * u) / (M : ℝ) ^ (1 / 3 : ℝ) := by sorry

end SpikedWishart.SoftEdge

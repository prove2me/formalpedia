-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_proposition_3_1
-- name    : SpikedWishart.SoftEdge.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:40:08.578298+00:00
-- url     : https://prove2.me/theorems/13dd0fd1-9a15-4ba5-a216-8c1e41df00ce
-- title:
--   Proposition 3.1, pp. 1663–1664 — |Z_M𝓗(u) − 𝓗∞(u)| ≤ Ce^{−cu}/M^{1/3} and |𝓙(v)/Z_M − 𝓙∞(v)| ≤ Ce^{−cv}/M^{1/3}
-- statement:
--   Fix $\varepsilon>0$, $\gamma_0\ge1$, a margin $c_0>0$ and integers $0\le k\le r$. For $M,N$ with $N\ge r$ and $\gamma=\sqrt{M/N}\in[1,\gamma_0]$, let $\pi_1=\dots=\pi_k=p_c$ and $\pi_{k+1},\dots,\pi_r$ with $c_0\le\pi_\ell^{-1}\le1+\gamma^{-1}-c_0$; set $q=p_c-\varepsilon/(\nu M^{1/3})$ (118), and define $\mathcal H,\mathcal J$ by (103)–(104), $Z_M$ by (116) and $\mathcal H_\infty,\mathcal J_\infty$ by (120), (122). Here $\Gamma$ is any circle with real centre enclosing $p_c$, $\pi_{k+1},\dots,\pi_r$ and $1$ and lying in $\{\mathrm{Re}\,z>q\}$; $\Sigma$ is any circle with real centre enclosing $0$ and lying in $\{\mathrm{Re}\,z<q\}$; $\Gamma_\infty$ has its vertex in $(-\varepsilon,0)$ and $\Sigma_\infty$ its vertex in $(-\infty,-\varepsilon)$. Then:
--
--   1. for every $U\in\mathbb R$ there are $C,c,M_0>0$ such that for all such data with $M\ge M_0$ and all $u\ge U$,
--   $$
--   \big|Z_M\mathcal H(u)-\mathcal H_\infty(u)\big|\le\frac{Ce^{-cu}}{M^{1/3}};
--   $$
--   2. for every $V\in\mathbb R$ there are $C,c,M_0>0$ such that for all such data with $M\ge M_0$ and all $v\ge V$,
--   $$
--   \Big|\frac1{Z_M}\mathcal J(v)-\mathcal J_\infty(v)\Big|\le\frac{Ce^{-cv}}{M^{1/3}} .
--   $$
--
--   These estimates give the convergence of the rescaled kernel of Proposition 2.1 to the limit kernel $\int_0^\infty\mathcal H_\infty(u+y)\mathcal J_\infty(v+y)\,dy$, in a norm strong enough for Fredholm determinants.
--
--   **Formalization Note** The constants are uniform over $\gamma\in[1,\gamma_0]$, over the spikes in the margin $c_0$ and over the admissible contours, which is how "for $\gamma$ in a compact subset of $[1,\infty)$" and "in a compact subset of $(0,1+\gamma^{-1})$" are read. The contours of §2 are circles (the integrals do not depend on the choice); $\Gamma$ is required to enclose $1$, the value of $\pi_j$ for $j>r$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1660–1664, (103)–(107), (116)–(122), Proposition 3.1, (123)–(124)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy
import Definitions.Def_SpikedWishart_SoftEdge_Kernels

namespace SpikedWishart.SoftEdge

theorem proposition_3_1 (ε γ₀ c₀ : ℝ) (hε : 0 < ε) (hγ₀ : 1 ≤ γ₀) (hc₀ : 0 < c₀)
    (r k : ℕ) (hkr : k ≤ r) :
    (∀ U₀ : ℝ, ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < M₀ ∧
      ∀ (M N : ℕ) (γ : ℝ) (π : Fin r → ℝ) (cΓ ρΓ cH u : ℝ),
        M₀ ≤ M → r ≤ N → γ = Real.sqrt ((M : ℝ) / (N : ℝ)) → 1 ≤ γ → γ ≤ γ₀ →
        (∀ j : Fin r, (j : ℕ) < k → π j = pc γ) →
        (∀ j : Fin r, k ≤ (j : ℕ) → c₀ ≤ (π j)⁻¹ ∧ (π j)⁻¹ ≤ 1 + γ⁻¹ - c₀) →
        |pc γ - cΓ| < ρΓ → (∀ j, |π j - cΓ| < ρΓ) → |1 - cΓ| < ρΓ → qM γ ε M < cΓ - ρΓ →
        -ε < cH → cH < 0 → U₀ ≤ u →
        ‖ZM γ (qM γ ε M) M k π * Hcal γ (qM γ ε M) M k π cΓ ρΓ u - Hinf ε k cH u‖ ≤
          C * Real.exp (-c * u) / (M : ℝ) ^ (1 / 3 : ℝ)) ∧
    (∀ V₀ : ℝ, ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < M₀ ∧
      ∀ (M N : ℕ) (γ : ℝ) (π : Fin r → ℝ) (cS ρS cJ v : ℝ),
        M₀ ≤ M → r ≤ N → γ = Real.sqrt ((M : ℝ) / (N : ℝ)) → 1 ≤ γ → γ ≤ γ₀ →
        (∀ j : Fin r, (j : ℕ) < k → π j = pc γ) →
        (∀ j : Fin r, k ≤ (j : ℕ) → c₀ ≤ (π j)⁻¹ ∧ (π j)⁻¹ ≤ 1 + γ⁻¹ - c₀) →
        |cS| < ρS → cS + ρS < qM γ ε M →
        cJ < -ε → V₀ ≤ v →
        ‖Jcal γ (qM γ ε M) M k π cS ρS v / ZM γ (qM γ ε M) M k π - Jinf ε k cJ v‖ ≤
          C * Real.exp (-c * v) / (M : ℝ) ^ (1 / 3 : ℝ)) := by sorry

end SpikedWishart.SoftEdge

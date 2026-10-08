-- Prove2me | Theorems.Thm_SpikedWishart_Separated_proposition_4_1
-- name    : SpikedWishart.Separated.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:47.024979+00:00
-- url     : https://prove2.me/theorems/b3bcf53a-fa8f-4b57-85ac-69e441f95a7f
-- title:
--   Proposition 4.1, pp. 1679–1680 — |𝓙(v)/Z_M − 𝓙_∞(v)| ≤ Ce^{−cv}/√M and |Z_M 𝓗(u) − 𝓗_∞(u)| ≤ Ce^{−cu}/√M
-- statement:
--   Fix $k \ge 1$, $m \ge 0$ ($r = k + m$), $\varepsilon > 0$, $\gamma_0 \ge 1$, $c_0 > 0$ and $C_0$. For $M, N \ge 1$ put $\gamma = \sqrt{M/N}$, let $\pi_1 \in [c_0, \gamma/(1+\gamma) - c_0]$ and $\pi_{k+1},\dots,\pi_r \in [\pi_1 + c_0, C_0]$, set $q$ by (220), and let $\mathcal H$, $\mathcal J$, $Z_M$, $\mathcal H_\infty$, $\mathcal J_\infty$ be as in (213), (214), (222), (221).
--
--   1. For any fixed $V \in \mathbb R$ there are constants $C, c, M_0 > 0$ such that
--   $$
--   \Big|\frac1{Z_M}\mathcal J(v) - \mathcal J_\infty(v)\Big| \le \frac{Ce^{-cv}}{\sqrt M}
--   $$
--   for all $v \ge V$, whenever $M \ge M_0$ and $1 \le \gamma \le \gamma_0$.
--   2. For any fixed $U \in \mathbb R$ there are constants $C, c, M_0 > 0$ such that
--   $$
--   \big|Z_M\mathcal H(u) - \mathcal H_\infty(u)\big| \le \frac{Ce^{-cu}}{\sqrt M}
--   $$
--   for all $u \ge U$, whenever $M \ge M_0$ and $1 \le \gamma \le \gamma_0$.
--
--   In both parts the constants are uniform over the stated ranges of $\gamma$, $\pi_1$ and $\pi_{k+1},\dots,\pi_r$.
--
--   This is the analytic core of the proof of Theorem 1.1(b): it gives Hilbert–Schmidt convergence of the two factors of the rescaled kernel, and hence convergence of the Fredholm determinant.
--
--   **Formalization Note** "$\gamma$ in a compact subset of $[1,\infty)$" is $\gamma \in [1,\gamma_0]$; the standing assumption (209) of §4 (that $\pi_1^{-1}$ and $\pi_\ell^{-1}$ lie in compact subsets of $(1+\gamma^{-1},\infty)$ and of $(0,\pi_1^{-1})$) is encoded by the margins $c_0, C_0$. The contours $\Gamma$, $\Sigma$ in $\mathcal H$, $\mathcal J$ are explicit circles; see the Kernels definition.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1679–1680, Proposition 4.1, (220)–(224)

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Kernels

namespace SpikedWishart.Separated

/-- Proposition 4.1, pp. 1679–1680. Fix `ε > 0`, `k ≥ 1`, `m = r − k`, and compact parameter
ranges `γ ∈ [1, γ₀]`, `π₁ ∈ [c₀, γ/(1+γ) − c₀]`, `π_{k+1}, …, π_r ∈ [π₁ + c₀, C₀]`, where
`γ = √(M/N)`. (i) For every `V` there are `C, c, M₀ > 0` with
`|𝓙(v)/Z_M − 𝓙_∞(v)| ≤ C e^{−cv}/√M` for `v ≥ V`, `M ≥ M₀`; (ii) for every `U` there are
`C, c, M₀ > 0` with `|Z_M 𝓗(u) − 𝓗_∞(u)| ≤ C e^{−cu}/√M` for `u ≥ U`, `M ≥ M₀`. -/
theorem proposition_4_1 (k m : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (γ₀ c₀ C₀ : ℝ)
    (hγ₀ : 1 ≤ γ₀) (hc₀ : 0 < c₀) :
    (∀ V : ℝ, ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < M₀ ∧
      ∀ (M N : ℕ), M₀ ≤ M → 1 ≤ gamMN M N → gamMN M N ≤ γ₀ →
      ∀ (π₁ : ℝ) (πo : Fin m → ℝ), c₀ ≤ π₁ → π₁ ≤ gamMN M N / (1 + gamMN M N) - c₀ →
        (∀ j, π₁ + c₀ ≤ πo j ∧ πo j ≤ C₀) → ∀ v : ℝ, V ≤ v →
          ‖(1 / ZM k πo ε π₁ M N) * JM k πo ε π₁ M N v - Jinf k ε v‖ ≤
            C * Real.exp (-c * v) / Real.sqrt M) ∧
    (∀ U : ℝ, ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < M₀ ∧
      ∀ (M N : ℕ), M₀ ≤ M → 1 ≤ gamMN M N → gamMN M N ≤ γ₀ →
      ∀ (π₁ : ℝ) (πo : Fin m → ℝ), c₀ ≤ π₁ → π₁ ≤ gamMN M N / (1 + gamMN M N) - c₀ →
        (∀ j, π₁ + c₀ ≤ πo j ∧ πo j ≤ C₀) → ∀ u : ℝ, U ≤ u →
          ‖ZM k πo ε π₁ M N * HM k πo ε π₁ M N u - Hinf k ε u‖ ≤
            C * Real.exp (-c * u) / Real.sqrt M) := by sorry

end SpikedWishart.Separated

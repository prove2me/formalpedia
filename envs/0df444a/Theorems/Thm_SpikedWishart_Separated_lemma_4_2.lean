-- Prove2me | Theorems.Thm_SpikedWishart_Separated_lemma_4_2
-- name    : SpikedWishart.Separated.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:40.705515+00:00
-- url     : https://prove2.me/theorems/e5fad3e8-7d36-431a-8091-2190a5fdafe7
-- title:
--   Lemma 4.2, p. 1686 — Re(f − f(π₁)) ≤ −c on Γ₁ ∪ Γ₂, Re f decreasing on Γ₃ ∪ Γ₄, and (265) on Γ₅ for large R
-- statement:
--   Let $\gamma_0 \ge 1$, $c_0 > 0$, $C_0 \in \mathbb R$ and $m \in \mathbb N$. Consider $\gamma \in [1,\gamma_0]$, $\pi_1 \in [c_0, \gamma/(1+\gamma) - c_0]$, and $\pi_{k+1},\dots,\pi_r \in [\pi_1 + c_0, C_0]$ ($r - k = m$), with $\mu$ as in (211), $f$ the phase (215) for any $q$, and $\pi_* = \min\{\pi_{k+1},\dots,\pi_r,1,1/(\mu\pi_1)\}$. Then there exist $\delta \in (0, 1/(1+\gamma_0))$, $c > 0$ and $R_0 > \max\{1, C_0\}$, not depending on $\gamma, \pi_1, \pi_{k+1},\dots,\pi_r, q$, such that, with $x_0,\theta_0$ defined by $x_0 + i\delta = 1 + \frac1{1+\gamma}e^{i(\pi-\theta_0)}$ (262):
--
--   1. (264) $\operatorname{Re}(f(z) - f(\pi_1)) \le -c$ for $z \in \Gamma_1 = \{\frac{\pi_1+\pi_*}2 + iy : 0 \le y \le \delta\}$ and for $z$ on $\Gamma_2$, the horizontal segment at height $\delta$ from $\frac{\pi_1+\pi_*}2 + i\delta$ to $x_0 + i\delta$;
--   2. $\operatorname{Re} f(z)$ decreases along $\Gamma_3 = \{1 + \frac1{1+\gamma}e^{i(\pi-\theta)} : \theta_0 \le \theta \le \pi/2\}$ as $\theta$ increases, and along $\Gamma_4 = \{x + \frac{i}{1+\gamma} : x \ge 1\}$ as $x$ increases;
--   3. (265) for every $R \ge R_0$ and $z \in \Gamma_5 = \{R + i(\frac1{1+\gamma} - y) : 0 \le y \le \frac1{1+\gamma}\}$,
--   $$
--   \operatorname{Re}\big(f(z) - f(\pi_1)\big) \le \operatorname{Re}\Big(f\Big(1 + \frac{i}{1+\gamma}\Big) - f(\pi_1)\Big).
--   $$
--
--   These estimates show that the contour $\Gamma'$ built from $\Gamma_1,\dots,\Gamma_5$ and their reflections, which encloses the poles of $g$ but not $\pi_1$, carries only an exponentially small contribution to $\mathcal H$.
--
--   **Formalization Note** "$\gamma$ in a compact subset of $[1,\infty)$" and "$\pi_1$ in a compact subset of $(0,\gamma/(1+\gamma))$" are encoded by $\gamma \in [1,\gamma_0]$ and the margin $c_0$; the remaining $\pi_\ell$ lie in a compact subset of $(\pi_1,\infty)$, encoded by $[\pi_1 + c_0, C_0]$. The bound $\delta < 1/(1+\gamma_0)$ makes (262) solvable. $\Gamma_2$ is stated on the segment joining its two endpoints in either order. $\Gamma_4$ is stated on the whole ray $x \ge 1$, which covers $1 \le x \le R$ for every $R$. The phase differences do not depend on $q$, so $q$ is arbitrary.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1685, (257)–(262); p. 1686, Lemma 4.2, (264)–(265)

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Phase

open Set Complex

namespace SpikedWishart.Separated

/-- Lemma 4.2, p. 1686. For `γ ∈ [1, γ₀]`, `π₁ ∈ [c₀, γ/(1+γ) − c₀]` and
`π_{k+1}, …, π_r ∈ [π₁ + c₀, C₀]` there are `δ > 0` (with `δ < 1/(1+γ₀)`, so that (262)
defines `x₀`, `θ₀`), `c > 0` and `R₀ > max{π_{k+1}, …, π_r, 1}` such that
(264) `Re(f(z) − f(π₁)) ≤ −c` on `Γ₁ = {(π₁+π_*)/2 + iy : 0 ≤ y ≤ δ}` and on the segment `Γ₂`
from `(π₁+π_*)/2 + iδ` to `x₀ + iδ`; `Re f` decreases along `Γ₃ = {1 + (1+γ)⁻¹e^{i(π−θ)} :
θ₀ ≤ θ ≤ π/2}` (as `θ` increases) and along `Γ₄ = {x + i/(1+γ) : x ≥ 1}` (as `x` increases);
and (265) holds on `Γ₅ = {R + i(1/(1+γ) − y) : 0 ≤ y ≤ 1/(1+γ)}` for every `R ≥ R₀`. -/
theorem lemma_4_2 (m : ℕ) (γ₀ c₀ C₀ : ℝ) (hγ₀ : 1 ≤ γ₀) (hc₀ : 0 < c₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / (1 + γ₀) ∧ ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ, 1 < R₀ ∧ C₀ < R₀ ∧
      ∀ (γ π₁ q : ℝ) (πo : Fin m → ℝ), 1 ≤ γ → γ ≤ γ₀ → c₀ ≤ π₁ → π₁ ≤ γ / (1 + γ) - c₀ →
        (∀ j, π₁ + c₀ ≤ πo j ∧ πo j ≤ C₀) →
        (∀ y ∈ Icc 0 δ,
          (fPhase γ π₁ q (((π₁ + piStar γ π₁ πo) / 2 : ℝ) + y * I) - fPhase γ π₁ q π₁).re ≤ -c) ∧
        (∀ x ∈ uIcc ((π₁ + piStar γ π₁ πo) / 2) (gX0 γ δ),
          (fPhase γ π₁ q (x + δ * I) - fPhase γ π₁ q π₁).re ≤ -c) ∧
        AntitoneOn
          (fun θ : ℝ => (fPhase γ π₁ q
            (1 + ((1 / (1 + γ) : ℝ) : ℂ) * cexp (((Real.pi - θ : ℝ) : ℂ) * I))).re)
          (Icc (theta0 γ δ) (Real.pi / 2)) ∧
        AntitoneOn (fun x : ℝ => (fPhase γ π₁ q (x + ((1 / (1 + γ) : ℝ) : ℂ) * I)).re) (Ici 1) ∧
        ∀ R : ℝ, R₀ ≤ R → ∀ y ∈ Icc 0 (1 / (1 + γ)),
          (fPhase γ π₁ q (R + ((1 / (1 + γ) - y : ℝ) : ℂ) * I) - fPhase γ π₁ q π₁).re ≤
            (fPhase γ π₁ q (1 + ((1 / (1 + γ) : ℝ) : ℂ) * I) - fPhase γ π₁ q π₁).re := by sorry

end SpikedWishart.Separated

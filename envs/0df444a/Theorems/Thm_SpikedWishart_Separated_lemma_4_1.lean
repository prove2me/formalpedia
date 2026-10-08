-- Prove2me | Theorems.Thm_SpikedWishart_Separated_lemma_4_1
-- name    : SpikedWishart.Separated.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:43.775113+00:00
-- url     : https://prove2.me/theorems/6967fa28-9e86-4561-a207-603706c088cd
-- title:
--   Lemma 4.1, pp. 1680–1681 — Re(−f) decreases along Σ₁ ∪ Σ₂, and for large R, max over Σ₃ of Re(−f) ≤ Re(−f) at the corner
-- statement:
--   Let $\varepsilon > 0$, $M \ge 1$, $\gamma \ge 1$, $0 < \pi_1 < \gamma/(1+\gamma)$, let $\mu,\nu$ be as in (211), $q = \pi_1 - \varepsilon/(\nu\sqrt M)$ (220), $f$ the phase (215), and $x_0 = \pi_1 - 2\varepsilon/(\nu\sqrt M)$. Consider the contour pieces
--   $$
--   \Sigma_1 = \{x_0 + iy : 0 \le y \le 2\},\quad \Sigma_2 = \Big\{\pi_1 + 2i - x : \tfrac{2\varepsilon}{\nu\sqrt M} \le x \le R\Big\},\quad \Sigma_3 = \{\pi_1 - R + i(2-y) : 0 \le y \le 2\}.
--   $$
--
--   1. If $x_0 > 0$, then $\operatorname{Re}(-f(z))$ decreases as $z$ moves up $\Sigma_1$ (as $y$ increases), and decreases as $z$ moves left along $\Sigma_2$ (as $x$ increases), for every $R$.
--   2. Let $\gamma_0 \ge 1$ and $c_0 > 0$. There is $R_0 > 0$ such that for every $R \ge R_0$, every $\gamma \in [1,\gamma_0]$, every $\pi_1 \in [c_0, \gamma/(1+\gamma) - c_0]$, every $M \ge 1$ and every $z \in \Sigma_3$,
--   $$
--   \operatorname{Re}(-f(z)) \le \operatorname{Re}\big(-f(x_0 + 2i)\big).
--   $$
--
--   These monotonicity properties make the closed contour $\Sigma$ built from $\Sigma_1,\Sigma_2,\Sigma_3$ and their reflections a steepest-descent contour for $\mathcal J$.
--
--   **Formalization Note** The page names the comparison point $p_* = \pi_1 + 2i$ and calls it the intersection of $\Sigma_1$ and $\Sigma_2$; by the definitions of $\Sigma_1$ and $\Sigma_2$ that intersection is $x_0 + 2i$, and the bound is stated there. Since $\operatorname{Re}(-f)$ decreases along $\Sigma_2$, this also gives the bound at $\pi_1 + 2i$. The hypothesis $x_0 > 0$ in part 1 is used in the paper's proof ("as $0 < x_0 < \pi_1$") and holds for large $M$. In part 2, "γ in a compact subset of $[1,\infty)$" is $\gamma \in [1,\gamma_0]$, and $\pi_1$ ranges over a compact subset of $(0,\gamma/(1+\gamma))$ given by the margin $c_0$; $R_0$ is uniform in $M$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1680–1681, Lemma 4.1, (225)–(229)

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Phase

open Set Complex

namespace SpikedWishart.Separated

/-- Lemma 4.1, pp. 1680–1681, with `q` of (220) and `x₀ = π₁ − 2ε/(ν√M)`.
(i) For `γ ≥ 1` and `0 < x₀`: `Re(−f)` decreases along `Σ₁ = {x₀ + iy : 0 ≤ y ≤ 2}` (upwards)
and along `Σ₂ = {π₁ + 2i − x : 2ε/(ν√M) ≤ x ≤ R}` (leftwards), for every `R`.
(ii) For `γ ∈ [1, γ₀]` and `π₁ ∈ [c₀, γ/(1+γ) − c₀]` there is `R₀` such that for `R ≥ R₀`,
`max_{Σ₃} Re(−f) ≤ Re(−f(x₀ + 2i))`, `Σ₃ = {π₁ − R + i(2 − y) : 0 ≤ y ≤ 2}`, uniformly in
`γ, π₁` and `M ≥ 1`. (The page names the corner `p_* = π₁ + 2i`; the intersection of `Σ₁`
and `Σ₂` is `x₀ + 2i`.) -/
theorem lemma_4_1 :
    (∀ (γ π₁ ε : ℝ) (M : ℕ), 1 ≤ γ → 0 < π₁ → π₁ < γ / (1 + γ) → 0 < ε → 0 < M →
      0 < π₁ - 2 * ε / (nu γ π₁ * Real.sqrt M) →
      AntitoneOn
          (fun y : ℝ => (-fPhase γ π₁ (qM ε γ π₁ M)
            (((π₁ - 2 * ε / (nu γ π₁ * Real.sqrt M) : ℝ) : ℂ) + y * I)).re) (Icc 0 2) ∧
      ∀ R : ℝ, AntitoneOn
          (fun x : ℝ => (-fPhase γ π₁ (qM ε γ π₁ M) ((π₁ : ℂ) + 2 * I - x)).re)
          (Icc (2 * ε / (nu γ π₁ * Real.sqrt M)) R)) ∧
    (∀ (γ₀ c₀ ε : ℝ), 1 ≤ γ₀ → 0 < c₀ → 0 < ε →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ (γ π₁ : ℝ) (M : ℕ), 1 ≤ γ → γ ≤ γ₀ →
        c₀ ≤ π₁ → π₁ ≤ γ / (1 + γ) - c₀ → 0 < M → ∀ y ∈ Icc (0 : ℝ) 2,
          (-fPhase γ π₁ (qM ε γ π₁ M) ((π₁ - R : ℝ) + (2 - y : ℝ) * I)).re ≤
            (-fPhase γ π₁ (qM ε γ π₁ M)
              (((π₁ - 2 * ε / (nu γ π₁ * Real.sqrt M) : ℝ) : ℂ) + 2 * I)).re) := by sorry

end SpikedWishart.Separated

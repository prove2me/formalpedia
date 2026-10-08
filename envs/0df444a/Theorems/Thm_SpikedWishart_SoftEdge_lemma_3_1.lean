-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_lemma_3_1
-- name    : SpikedWishart.SoftEdge.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:40:03.667995+00:00
-- url     : https://prove2.me/theorems/63a303dd-9cb5-4835-abca-fa32af976ab9
-- title:
--   Lemma 3.1, p. 1665 — Re f decreases along Γ₁ ∪ Γ₂, and max over Γ₃ is at most Re f(p∗)
-- statement:
--   Let $f$, $\nu$, $p_c$ be as in (101)–(106), with any real $q$. For $\varepsilon>0$ and $M\ge1$ consider the contour pieces
--   $$
--   \Gamma_1=\Big\{p_c+te^{i\pi/3}:\tfrac{\varepsilon}{2\nu M^{1/3}}\le t\le2(1-p_c)\Big\},\quad
--   \Gamma_2=\{p_*+x:0\le x\le R\},\quad
--   \Gamma_3=\{1+R+iy:0\le y\le\sqrt3(1-p_c)\},
--   $$
--   with $p_*=p_c+2(1-p_c)e^{i\pi/3}$, the common point of $\Gamma_1$ and $\Gamma_2$. Then:
--
--   1. for every $\gamma\ge1$, $\mathrm{Re}\,f$ is strictly decreasing along $\Gamma_1$ as $t$ increases and along $\Gamma_2$ as $x$ increases (for every $R\ge0$), i.e. along $\Gamma_1\cup\Gamma_2$ as $\mathrm{Re}\,z$ increases;
--   2. for every $\gamma_0\ge1$ there is $R_0>0$ such that for all $\gamma\in[1,\gamma_0]$ and all $R\ge R_0$,
--   $$
--   \max_{z\in\Gamma_3}\mathrm{Re}\,f(z)\le\mathrm{Re}\,f(p_*).
--   $$
--
--   These are the decay estimates that localise the integral $\mathcal H(u)$ near the critical point $p_c$.
--
--   **Formalization Note** "For $\gamma$ in a compact subset of $[1,\infty)$, we can take $R$ large enough" is read as: $R_0$ depends only on $\gamma_0$, and every $R\ge R_0$ works. $q$ shifts $\mathrm{Re}\,f$ by a constant, so the statements hold for every real $q$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1664–1665, (125)–(128), Lemma 3.1, (131)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex

namespace SpikedWishart.SoftEdge

theorem lemma_3_1 :
    (∀ (γ q ε : ℝ) (M : ℕ), 1 ≤ γ → 0 < ε → 0 < M →
      StrictAntiOn (fun t : ℝ => (fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp ((Real.pi / 3 : ℝ) * I))).re)
        (Set.Icc (ε / (2 * nu γ * (M : ℝ) ^ (1 / 3 : ℝ))) (2 * (1 - pc γ)))) ∧
    (∀ (γ q R : ℝ), 1 ≤ γ →
      StrictAntiOn
        (fun x : ℝ => (fFn γ q ((pc γ : ℂ) + 2 * (1 - pc γ) * exp ((Real.pi / 3 : ℝ) * I) + x)).re)
        (Set.Icc 0 R)) ∧
    (∀ γ₀ : ℝ, 1 ≤ γ₀ → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ (γ q R y : ℝ), 1 ≤ γ → γ ≤ γ₀ → R₀ ≤ R →
      0 ≤ y → y ≤ Real.sqrt 3 * (1 - pc γ) →
      (fFn γ q (1 + R + (y : ℂ) * I)).re ≤
        (fFn γ q ((pc γ : ℂ) + 2 * (1 - pc γ) * exp ((Real.pi / 3 : ℝ) * I))).re) := by sorry

end SpikedWishart.SoftEdge

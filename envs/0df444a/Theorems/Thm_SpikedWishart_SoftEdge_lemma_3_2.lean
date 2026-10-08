-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_lemma_3_2
-- name    : SpikedWishart.SoftEdge.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:40:14.313951+00:00
-- url     : https://prove2.me/theorems/32e13a45-303d-4e9c-a2ae-b725d5617a27
-- title:
--   Lemma 3.2, p. 1672 — Re(−f) decreases along Σ₁ ∪ Σ₂, and max over Σ₃ is at most Re(−f(p∗))
-- statement:
--   Let $f$, $\nu$, $p_c$ be as in (101)–(106), with any real $q$. For $\varepsilon>0$ and $M\ge1$ consider
--   $$
--   \Sigma_1=\Big\{p_c+te^{2i\pi/3}:\tfrac{3\varepsilon}{\nu M^{1/3}}\le t\le2p_c\Big\},\quad
--   \Sigma_2=\{p_*-x:0\le x\le R\},\quad
--   \Sigma_3=\{-R+i(\sqrt3p_c-y):0\le y\le\sqrt3p_c\},
--   $$
--   with $p_*=p_c+2p_ce^{2i\pi/3}$, the common point of $\Sigma_1$ and $\Sigma_2$. Then:
--
--   1. for every $\gamma\ge1$, $\mathrm{Re}(-f)$ is strictly decreasing along $\Sigma_1$ as $t$ increases and along $\Sigma_2$ as $x$ increases (for every $R\ge0$), i.e. along $\Sigma_1\cup\Sigma_2$ as $\mathrm{Re}\,z$ decreases;
--   2. for every $\gamma_0\ge1$ there is $R_0>0$, independent of $\gamma$, such that for all $\gamma\in[1,\gamma_0]$ and all $R\ge R_0$,
--   $$
--   \max_{z\in\Sigma_3}\mathrm{Re}(-f(z))\le\mathrm{Re}(-f(p_*)).
--   $$
--
--   These are the decay estimates that localise the integral $\mathcal J(v)$ near the critical point $p_c$.
--
--   **Formalization Note** The page's "(175) $\max_{z\in\sigma_3}$" is read as $\Sigma_3$. $R_0$ depends only on $\gamma_0$ and every $R\ge R_0$ works; the statements hold for every real $q$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1671–1672, (170)–(173), Lemma 3.2, (175)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex

namespace SpikedWishart.SoftEdge

theorem lemma_3_2 :
    (∀ (γ q ε : ℝ) (M : ℕ), 1 ≤ γ → 0 < ε → 0 < M →
      StrictAntiOn
        (fun t : ℝ => (-fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp ((2 * Real.pi / 3 : ℝ) * I))).re)
        (Set.Icc (3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ))) (2 * pc γ))) ∧
    (∀ (γ q R : ℝ), 1 ≤ γ →
      StrictAntiOn
        (fun x : ℝ => (-fFn γ q ((pc γ : ℂ) + 2 * pc γ * exp ((2 * Real.pi / 3 : ℝ) * I) - x)).re)
        (Set.Icc 0 R)) ∧
    (∀ γ₀ : ℝ, 1 ≤ γ₀ → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ (γ q R y : ℝ), 1 ≤ γ → γ ≤ γ₀ → R₀ ≤ R →
      0 ≤ y → y ≤ Real.sqrt 3 * pc γ →
      (-fFn γ q (-(R : ℂ) + ((Real.sqrt 3 * pc γ - y : ℝ) : ℂ) * I)).re ≤
        (-fFn γ q ((pc γ : ℂ) + 2 * pc γ * exp ((2 * Real.pi / 3 : ℝ) * I))).re) := by sorry

end SpikedWishart.SoftEdge

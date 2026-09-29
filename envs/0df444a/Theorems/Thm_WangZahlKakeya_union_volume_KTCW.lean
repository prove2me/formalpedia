-- Prove2me | Theorems.Thm_WangZahlKakeya_union_volume_KTCW
-- name    : WangZahlKakeya.union_volume_KTCW
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T14:16:08.786387+00:00
-- url     : https://prove2.me/theorems/b6b719d6-2c14-46bf-9d56-16ef66221ea5
-- title:
--   Volume bound with the Katz--Tao Convex Wolff constant (Wang--Zahl, Corollary 1.10)
-- statement:
--   **Restatement of the endpoint estimate.**
--
--   For every $\varepsilon>0$ there is $K$ such that for all sufficiently small $\delta>0$: if $(\mathbb{T},Y)_\delta$ is a nonempty $\lambda$-dense system of essentially distinct $\delta$-tubes in the unit ball, then
--
--   $$\Big|\bigcup_{T\in\mathbb{T}} Y(T)\Big| \;\ge\; \delta^{\varepsilon}\,\lambda^{K}\, m^{-1}\,(\#\mathbb{T})|T|, \qquad m = C_{\mathrm{KT\text{-}CW}}(\mathbb{T}).$$
--
--   This is the form of Theorem 1.9 used in applications: the density enters as a power $\lambda^K$ rather than through the $\delta^\eta$ normalization, and the only structural input is the Katz–Tao Convex Wolff constant. Theorem 1.2 is the special case in which the Wolff axioms force $m \le 1000$.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, p. 8, Corollary 1.10 (inequality (1.4))

import Definitions.Def_WangZahlKakeya_wolff

namespace WangZahlKakeya
open MeasureTheory Metric Set

theorem union_volume_KTCW :
    ∀ ε > (0 : ℝ), ∃ K > (0 : ℝ), ∃ δ₀ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3) (lam : ℝ),
        0 < n → IsTubeSystem δ n p v Y → 0 < lam → IsDenseSystem δ n Y lam →
        (volume (shadingUnion Y)).toReal ≥
          δ ^ ε * lam ^ K * (KTCW δ n p v)⁻¹ * ((n : ℝ) * tubeVol δ) := by sorry

end WangZahlKakeya

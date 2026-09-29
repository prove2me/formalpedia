-- Prove2me | Theorems.Thm_WangZahlKakeya_tubeSystem_card_le
-- name    : WangZahlKakeya.tubeSystem_card_le
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T14:46:41.470337+00:00
-- url     : https://prove2.me/theorems/d9085aac-8991-4ba1-ad9e-6cc229c3d838
-- title:
--   Cardinality bound $\#\mathbb{T} \lesssim \delta^{-4}$ for essentially distinct $\delta$-tubes
-- statement:
--   **A family of pairwise essentially distinct $\delta$-tubes in the unit ball has cardinality $O(\delta^{-4})$.**
--
--   There is an absolute constant $C > 0$ such that every system $(\mathbb{T}, Y)_\delta$ of pairwise essentially distinct $\delta$-tubes contained in the unit ball of $\mathbb{R}^3$ satisfies
--
--   $$\#\mathbb{T} \;\le\; C\,\delta^{-4}.$$
--
--   The bound reflects the fact that the set of lines meeting the unit ball is four-dimensional (two parameters for the direction, two for the position), and that two $\delta$-tubes whose parameters agree to within $\sim\delta$ overlap in more than half of their volume, hence fail to be essentially distinct. Wang--Zahl use this bound in the deduction of Theorem 1.9 from Propositions 1.6--1.8, where it is what allows an improvement in the parameter $\omega$ to be traded for an improvement in the parameter $\sigma$.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, p. 7, the paragraph following Proposition 1.7 (“since the collections of tubes in the definitions of $\mathcal{E}$ and $\mathcal{D}$ are essentially distinct and are contained in the unit ball, we always have $\#\mathbb{T}\lesssim\delta^{-4}$”)

import Definitions.Def_WangZahlKakeya_wolff

namespace WangZahlKakeya

theorem tubeSystem_card_le :
    ∃ C > (0 : ℝ), ∀ (δ : ℝ) (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3),
      IsTubeSystem δ n p v Y → (n : ℝ) ≤ C * δ ^ (-(4 : ℝ)) := by sorry

end WangZahlKakeya

-- Prove2me | Theorems.Thm_WangZahlKakeya_KTCW_pos
-- name    : WangZahlKakeya.KTCW_pos
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T15:04:03.482842+00:00
-- url     : https://prove2.me/theorems/2d56016a-4626-4b45-9683-cf7bcc2bb3ad
-- title:
--   The Katz--Tao Convex Wolff constant of a nonempty tube family is positive
-- statement:
--   **$C_{\mathrm{KT\text{-}CW}}(\mathbb{T}) > 0$ for a nonempty family of $\delta$-tubes.**
--
--   If $\mathbb{T}$ contains at least one tube $T$, then any admissible constant $C$ in Definition 1.3(A) must satisfy $C \ge |T|/|W|$ for $W$ the convex hull of $T$, a convex set of finite volume containing $T$; hence the infimum defining $C_{\mathrm{KT\text{-}CW}}(\mathbb{T})$ is strictly positive.
--
--   The statement matters because $C_{\mathrm{KT\text{-}CW}}(\mathbb{T})^{-1}$ appears as a factor in Corollary 1.10 and in Assertion $E(\sigma,\omega)$: without positivity, that factor would carry no information.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, p. 5, Definition 1.3(A) (the Katz--Tao Convex Wolff Axioms), used with Corollary 1.10 on p. 8

import Definitions.Def_WangZahlKakeya_wolff

namespace WangZahlKakeya

theorem KTCW_pos (δ : ℝ) (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3)
    (hT : IsTubeSystem δ n p v Y) (hn : 0 < n) : 0 < KTCW δ n p v := by sorry

end WangZahlKakeya

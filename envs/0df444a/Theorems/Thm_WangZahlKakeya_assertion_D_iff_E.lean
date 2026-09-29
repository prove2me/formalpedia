-- Prove2me | Theorems.Thm_WangZahlKakeya_assertion_D_iff_E
-- name    : WangZahlKakeya.assertion_D_iff_E
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T13:14:50.422195+00:00
-- url     : https://prove2.me/theorems/f7ed36bd-6389-44e4-95df-4e4e52964bdd
-- title:
--   Assertions $D(\sigma,\omega)$ and $E(\sigma,\omega)$ are equivalent (Wang--Zahl, Proposition 1.6)
-- statement:
--   **The two assertions are equivalent in the range $0 \le \sigma \le 2/3$.**
--
--   Let $0 \le \sigma \le 2/3$ and $\omega \ge 0$. Then
--
--   $$E(\sigma,\omega) \iff D(\sigma,\omega).$$
--
--   Assertion $E(\sigma,\omega)$ imposes no non-clustering hypothesis and instead carries the two Wolff constants $m = C_{\mathrm{KT\text{-}CW}}(\mathbb{T})$ and $\ell = C_{\mathrm{F\text{-}SW}}(\mathbb{T})$ in its conclusion, while $D(\sigma,\omega)$ assumes both constants are at most $\delta^{-\eta}$ and states the corresponding clean bound. The implication $E \Rightarrow D$ is immediate from the definitions; the substance is the converse, which the paper obtains by factoring a family of tubes through convex sets on which the Wolff constants are controlled.
--
--   This equivalence is what allows the induction on scales to be run on the more flexible assertion $E$ while the input and output of each step are stated for $D$.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, p. 7, Proposition 1.6 (proved in §6)

import Definitions.Def_WangZahlKakeya_assertions

namespace WangZahlKakeya

theorem assertion_D_iff_E (σ ω : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 2 / 3) (hω : 0 ≤ ω) :
    AssertionE σ ω ↔ AssertionD σ ω := by sorry

end WangZahlKakeya

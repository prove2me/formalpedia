-- Prove2me | Theorems.Thm_WangZahlKakeya_assertion_D_half_zero
-- name    : WangZahlKakeya.assertion_D_half_zero
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T14:13:09.951404+00:00
-- url     : https://prove2.me/theorems/c753b28f-d2a7-4c98-9712-97c01c79784f
-- title:
--   Hairbrush base case: $D(1/2,0)$ (Wang--Zahl, Proposition 1.8)
-- statement:
--   **The base case of the induction: $D(1/2, 0)$ is true.**
--
--   Explicitly: for every $\varepsilon > 0$ there are $\kappa,\eta>0$ so that every nonempty $\delta^\eta$-dense system $(\mathbb{T},Y)_\delta$ of essentially distinct $\delta$-tubes in the unit ball whose Katz–Tao Convex Wolff and Frostman Slab Wolff constants are both at most $\delta^{-\eta}$ satisfies
--
--   $$\Big|\bigcup_{T\in\mathbb{T}} Y(T)\Big| \;\ge\; \kappa\,\delta^{\varepsilon}\,(\#\mathbb{T})|T|\,\big((\#\mathbb{T})|T|^{1/2}\big)^{-1/2}.$$
--
--   This is a shaded, Wolff-axiom form of Wolff's hairbrush bound, which gives Hausdorff dimension $\ge (n+2)/2$ for Kakeya sets in $\mathbb{R}^n$ and hence $\ge 5/2$ in $\mathbb{R}^3$. It provides the starting point from which Propositions 1.6 and 1.7 iterate down to the sharp endpoint $D(0,0)$.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, p. 7, Proposition 1.8 (proved in Appendix B)

import Definitions.Def_WangZahlKakeya_assertions

namespace WangZahlKakeya

theorem assertion_D_half_zero : AssertionD (1 / 2) 0 := by sorry

end WangZahlKakeya

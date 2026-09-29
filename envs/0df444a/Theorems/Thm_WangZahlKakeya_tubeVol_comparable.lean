-- Prove2me | Theorems.Thm_WangZahlKakeya_tubeVol_comparable
-- name    : WangZahlKakeya.tubeVol_comparable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T14:46:40.031607+00:00
-- url     : https://prove2.me/theorems/13a2a2f7-64a9-4b3d-9b6f-607430956a99
-- title:
--   The volume of a $\delta$-tube satisfies $|T| \sim \delta^2$
-- statement:
--   **The volume of a $\delta$-tube is comparable to $\delta^2$.**
--
--   Throughout Wang--Zahl, $|T|$ denotes the common volume of a $\delta$-tube, that is, of the closed $\delta$-neighbourhood of a unit line segment in $\mathbb{R}^3$, and the standing convention of the paper is that *$|T|$ has size about $\delta^2$*. This statement makes that convention quantitative: for every $0 < \delta \le 1$,
--
--   $$3\delta^2 \;\le\; |T| \;\le\; 8\delta^2 .$$
--
--   The tube is a spherocylinder — a circular cylinder of radius $\delta$ and height $1$ capped at both ends by half-balls of radius $\delta$ — so in fact $|T| = \pi\delta^2 + \tfrac{4}{3}\pi\delta^3$, and the two displayed bounds follow from $3 < \pi$ and $\pi(1 + \tfrac43\delta) \le \tfrac{7\pi}{3} < 8$ for $\delta \le 1$. The particular constants $3$ and $8$ are immaterial; what matters downstream is that $|T|^{1/2}$ is comparable to $\delta$.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, p. 5, the conventions of §1.2 preceding Definition 1.3 (“$|T|$ will denote the volume of a $\delta$-tube, i.e. $|T|$ has size about $\delta^2$”)

import Definitions.Def_WangZahlKakeya_wolff

namespace WangZahlKakeya

theorem tubeVol_comparable (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    3 * δ ^ 2 ≤ tubeVol δ ∧ tubeVol δ ≤ 8 * δ ^ 2 := by sorry

end WangZahlKakeya

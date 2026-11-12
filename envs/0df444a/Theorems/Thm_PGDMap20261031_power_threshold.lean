-- Prove2me | Theorems.Thm_PGDMap20261031_power_threshold
-- name    : PGDMap20261031.power_threshold
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:03:57.454301+00:00
-- url     : https://prove2.me/theorems/42737d46-8bb5-4759-b1d2-a65ca8ede81a
-- title:
--   Lemma 3: the power-curvature threshold and one-turning-point structure
-- statement:
--   ## Statement
--
--   For real $c,t$, define $Q_c(t)=\big((1+t)^{-c}+(1-t)^{-c}\big)/2$, where powers are the code's total real-power operation. For real $a,c,u$, put $T_{a,c}(u)=(1-au)Q_c(\sqrt u)$ and $\tau(a)=(\sqrt{1+8a}-1)/2$, with the total real square root. The theorem asserts the following. For every real $a,c$ with $0<a<1$ and $0<c<1$, both of the following implications hold: if $\tau(a)\le c$, then $T_{a,c}(s)<T_{a,c}(t)$ for every $0\le s<t<1$; if $c<\tau(a)$, then there is a real $u$ with $0<u<1$ such that $T_{a,c}(t)<T_{a,c}(s)$ whenever $0\le s<t\le u$, and $T_{a,c}(s)<T_{a,c}(t)$ whenever $u\le s<t<1$.
-- source:
--   Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures, manuscript dated 2026-10-30, Lemma 3, p. 3; local source: 03_Jointly_Optimal_Bregman_Map_and_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Entropy
open PGDMap20261031

theorem PGDMap20261031.power_threshold : PowerThresholdClaim := by sorry

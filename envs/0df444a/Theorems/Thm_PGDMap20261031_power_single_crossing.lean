-- Prove2me | Theorems.Thm_PGDMap20261031_power_single_crossing
-- name    : PGDMap20261031.power_single_crossing
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:03:57.840288+00:00
-- url     : https://prove2.me/theorems/bcdda48f-c5b9-41bd-9052-c92171774eb8
-- title:
--   Lemma 2: single crossing of scaled power curvatures
-- statement:
--   ## Statement
--
--   For real $c,t$, define $Q_c(t)=\big((1+t)^{-c}+(1-t)^{-c}\big)/2$, where powers are the code's total real-power operation. The theorem asserts the following. For every real $c_1,c_2$ with $0\le c_1<c_2\le2$, and every pair of real numbers $s,t$ with $0\le s<t<1$, $Q_{c_2}(s)/Q_{c_1}(s)<Q_{c_2}(t)/Q_{c_1}(t)$.
-- source:
--   Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures, manuscript dated 2026-10-30, Lemma 2, pp. 2-3; local source: 03_Jointly_Optimal_Bregman_Map_and_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Entropy
open PGDMap20261031

theorem PGDMap20261031.power_single_crossing : PowerSingleCrossingClaim := by sorry

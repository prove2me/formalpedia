-- Prove2me | Theorems.Thm_WeilDefect_RPB108_source_cross_square_of_gram_domination
-- name    : WeilDefect.RPB108.source_cross_square_of_gram_domination
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:58:46.113244+00:00
-- url     : https://prove2.me/theorems/2644cacc-5d72-45ef-847e-ab08a216cf41
-- title:
--   Source pairing transport through Gram domination
-- statement:
--   Let $q\in\mathbb C$ and $c,\rho,G,V\in\mathbb R$. If $c\ge0$, $G\le\rho V$, and $|q|^2\le cG$, then
--
--   $$|q|^2\le(c\rho)V.$$
--
--   This scalar transport keeps the source pairing bound explicit; no additional signs of $G,V,\rho$ are assumed.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/MixedPairing.lean#L5-L12; exact native theorem WeilDefect.RPB108.source_cross_square_of_gram_domination. SHA256 a93c990b29d50c5536f57ca66d5750c92cbb38320e8b1188887c2cfdfbf85428. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.source_cross_square_of_gram_domination (q : ℂ) (c rho G V : ℝ)
    (hc : 0 ≤ c) (hG : G ≤ rho*V) (hq : ‖q‖^2 ≤ c*G) :
    ‖q‖^2 ≤ (c*rho)*V := by sorry

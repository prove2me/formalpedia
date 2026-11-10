-- Prove2me | Theorems.Thm_StableCountSub3_lemma_B_5
-- name    : StableCountSub3.lemma_B_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:51:43.94681+00:00
-- url     : https://prove2.me/theorems/097a9778-341b-404b-bb8c-63d8f9becee8
-- title:
--   Lemma B.5 — numerical certificates for 3.332, 3.060 and 2.999
-- statement:
--   With $C_0=\sum_{j\ge1}\frac{2\log j}{(j+1)(j+2)}$ and $\delta_d=\sum_{j\ge d}\frac{2\log\frac{j+1}{j}}{(j+1)(j+2)(j+3)}$ (natural logarithms):
--   $C_0<\log(3.332)$, $C_0-\frac23(\delta_1+2\delta_2)<\log(3.060)$, and $C_0-\frac23(\delta_1+2\delta_2)-4\delta_4<\log(2.999)$.
--
--   Differences from the source:
--   - encoding: the series C0 and δ_d, the decimals 3.332, 3.060, 2.999 → tsums with indices shifted to start at 0; the decimals as exact real literals (3332/1000 etc.); reason: Lean convention; same numbers (the series converge)
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma B.5, p. 50 (PDF 52)

import Mathlib
import Definitions.Def_StableCountSub3_Savings

namespace StableCountSub3

/-- Lemma B.5 (numerical certificates), natural logarithms. -/
theorem lemma_B_5 :
    C0 < Real.log 3.332 ∧
    C0 - 2 / 3 * (delta 1 + 2 * delta 2) < Real.log 3.060 ∧
    C0 - 2 / 3 * (delta 1 + 2 * delta 2) - 4 * delta 4 < Real.log 2.999 := by sorry

end StableCountSub3

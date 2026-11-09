-- Prove2me | Theorems.Thm_TriFreeEst247_Main_proposition_2_6
-- name    : TriFreeEst247.Main.proposition_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:01:42.452907+00:00
-- url     : https://prove2.me/theorems/c4f37200-940f-4e29-9a0b-020ec4ba86c0
-- title:
--   Proposition 2.6: removal parameter versus testing
-- statement:
--   There are absolute constants $c,C>0$ such that for every $0<\varepsilon<1/4$,
--
--   $$cT_\triangle(\varepsilon)\le R_\triangle(\varepsilon)\le CT_\triangle(\varepsilon)^6.$$
--
--   Both the lower comparison and the sixth-power upper comparison concern the optimal two-sided testing complexity, uniform over all graph orders. This relates the removal parameter to the query complexity without assuming either conclusion as algorithmic data.
--
--   Differences from the source:
--   - encoding: minimum query counts and the real removal bound → extended-natural query minima embedded in ENNReal, and an ENNReal removal infimum; reason: this preserves finite values and uses infinity only when a feasible bound does not exist
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.9, Proposition 2.6

import Mathlib
import Definitions.Def_TriFreeEst247_Main_GraphModel

open scoped ENNReal

namespace TriFreeEst247.Main

theorem proposition_2_6 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      ENNReal.ofReal c * (testingComplexity ε).toENNReal ≤ removalParameter ε ∧
      removalParameter ε ≤ ENNReal.ofReal C * (testingComplexity ε).toENNReal^6 := by sorry

end TriFreeEst247.Main

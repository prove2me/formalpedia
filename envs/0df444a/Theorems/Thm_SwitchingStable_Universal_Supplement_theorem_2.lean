-- Prove2me | Theorems.Thm_SwitchingStable_Universal_Supplement_theorem_2
-- name    : SwitchingStable.Universal.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:36:53.502887+00:00
-- url     : https://prove2.me/theorems/5890314d-82e6-44e4-af88-3033ce9ab0a0
-- title:
--   Theorem 2 — exact counts for Tables 4–8 and five extremal lower bounds
-- statement:
--   For the five complete strict instances $I_7,I_9,I_{11},I_{13},I_{15}$ given by Tables 4–8, write $N(I)$ for the number of all stable perfect matchings and $x_n$ for the maximum over all complete strict markets of size $n$. Then
--
--   $$N(I_7)=85,\quad N(I_9)=388,\quad N(I_{11})=1790,\quad N(I_{13})=8048,\quad N(I_{15})=35525,$$
--   $$x_7\ge85,\quad x_9\ge388,\quad x_{11}\ge1790,\quad x_{13}\ge8048,\quad x_{15}\ge35525.$$
--
--   Both the five exact counts and the five lower bounds are asserted. These finite constructions are companion results, independent of the proof of the mission's universal goal.
--
--   Differences from the source:
--   - encoding: one-based preference tables and x_n → inverse permutations on Fin n and published SM n; reason: relabels every complete strict instance bijectively and preserves all ten assertions
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 12, PDF p. 13, Theorem 2; Section 6 and Appendices G–I

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Supplement_Tables

namespace SwitchingStable.Universal.Supplement

theorem theorem_2 :
    StableCount.numStable table7 = 85 ∧ StableCount.numStable table9 = 388 ∧
    StableCount.numStable table11 = 1790 ∧ StableCount.numStable table13 = 8048 ∧
    StableCount.numStable table15 = 35525 ∧
    85 ≤ StableCount.SM 7 ∧ 388 ≤ StableCount.SM 9 ∧ 1790 ≤ StableCount.SM 11 ∧
    8048 ≤ StableCount.SM 13 ∧ 35525 ≤ StableCount.SM 15 := by sorry

end SwitchingStable.Universal.Supplement

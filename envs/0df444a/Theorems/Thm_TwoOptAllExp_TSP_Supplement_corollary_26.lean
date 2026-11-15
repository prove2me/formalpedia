-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_corollary_26
-- name    : TwoOptAllExp.TSP.Supplement.corollary_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:52:48.29547+00:00
-- url     : https://prove2.me/theorems/2560d427-0ac8-414d-a41f-19171eb800a3
-- title:
--   Corollary 26 — every maximal run from $\sigma_0$ has length $T_n=(39\cdot3^n-35)/2$ and ends at the same local optimum
-- statement:
--   In the instance $I_n$ ($n\ge1$) of Section 5, every maximal improving flip sequence from the all-zero assignment $\sigma_0$ has length
--
--   $$T_n=\frac{39\cdot3^n-35}{2}$$
--
--   and ends at the same local optimum: the assignment in which every layer $F_0,\dots,F_n$ is in phase $1$ and $v'_0=v'_1=v'_2=0$.
--
--   Differences from the source:
--   - encoding: length T_n = (39·3^n − 35)/2 → length = T n, and the length cast to ℚ equals (39·3^n − 35)/2; reason: exact division
--   - encoding: the same local optimum, namely the described assignment → the final assignment is in phase 1 on F_0..F_n with v′_0 = v′_1 = v′_2 = 0; reason: the final assignment is a local optimum by maximality; equality to one fixed assignment gives "the same"
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Corollary 26, p. 35

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA232

namespace TwoOptAllExp.TSP.Supplement

open MCA232 MCA232.Vx

/-- **Corollary 26** (p. 35). All maximal improving flip sequences of `I_n` from `σ₀` have length
`T_n = (39 · 3^n - 35) / 2` and end at the same local optimum, namely the assignment in which every
layer `F_i` is in phase `1` and `v′_0 = v′_1 = v′_2 = 0`. -/
theorem corollary_26 (n : ℕ) (hn : 1 ≤ n) :
    ∀ ys : List (V n), IsMaximalFlipSeq (inst n).Φ (σ₀ n) ys →
      ys.length = T n ∧ (ys.length : ℚ) = (39 * 3 ^ n - 35) / 2 ∧
      InPhase (applyFlips (σ₀ n) ys) n true ∧
      val (applyFlips (σ₀ n) ys) (vp 0) = false ∧
      val (applyFlips (σ₀ n) ys) (vp 1) = false ∧
      val (applyFlips (σ₀ n) ys) (vp 2) = false := by sorry

end TwoOptAllExp.TSP.Supplement

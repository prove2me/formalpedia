-- Prove2me | Theorems.Thm_QAOAE3Lin2_General_eq_43
-- name    : QAOAE3Lin2.General.eq_43
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:29.558383+00:00
-- url     : https://prove2.me/theorems/bf4c974d-bfb3-46ed-a7e6-d59b2f296fce
-- title:
--   Section II, (42)–(43), p. 8 — for large D, some odd k ∈ [5 ln D, 5 ln D + 2] gives 1/(20D^{1/2}k) − (9/10)^{k+2} > 1/(101D^{1/2} ln D)
-- statement:
--   There is a threshold $D_0$ such that for every natural number $D\ge D_0$ there is an odd integer $k$ with $5\ln D\le k\le5\ln D+2$ and
--   $$\frac1{20D^{1/2}k}-\Big(\frac9{10}\Big)^{k+2}>\frac1{101D^{1/2}\ln D}.$$
--
--   This is the right-hand side of (42), divided by $m$, compared with (43). It fixes how many grid angles are needed.
--
--   **Formalization Note.** "For large $D$" is the existential threshold $D_0$; it is very large (the inequality first holds near $\ln D\approx573$), so it is not named. The page's "$k=5\ln D$" is pinned as an odd $k$ in $[5\ln D,5\ln D+2]$, because (39) needs $k$ odd and $5\ln D$ is not an integer.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 8, Section II, (42)–(43)

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

namespace QAOAE3Lin2.General

theorem eq_43 :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∃ k : ℕ, Odd k ∧ 5 * Real.log D ≤ k ∧
      (k : ℝ) ≤ 5 * Real.log D + 2 ∧
      1 / (101 * Real.sqrt D * Real.log D) < 1 / (20 * Real.sqrt D * k) - (9 / 10 : ℝ) ^ (k + 2) := by sorry

end QAOAE3Lin2.General

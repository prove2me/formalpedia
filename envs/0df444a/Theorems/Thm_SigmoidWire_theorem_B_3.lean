-- Prove2me | Theorems.Thm_SigmoidWire_theorem_B_3
-- name    : SigmoidWire.theorem_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:19.488423+00:00
-- url     : https://prove2.me/theorems/a6973c85-c241-4ca6-9611-88cbddc3ddb0
-- title:
--   Theorem B.3: Newman's rational approximation of $|y|$
-- statement:
--   There is an absolute constant $C_N$ such that for every integer $n\ge1$ there is a rational function $N_n$ of degree at most $n$, with no pole in $[-1,1]$, such that
--
--   $$
--   \bigl|N_n(y)-|y|\bigr|\le C_N\,e^{-\sqrt n}\qquad\text{for all }y\in[-1,1].
--   $$
--
--   This classical theorem of Newman is the source of the degree $O(\ln^2(a/\varepsilon))$ in the rational approximation of Sigmoid.
--
--   Differences from the source:
--   - encoding: a rational function Nₙ with the bound for all y ∈ [−1, 1] → polynomials P, Q of degree ≤ n with Q ≠ 0 on [−1, 1]; reason: the bound presupposes that Nₙ is defined on [−1, 1]; in Lean P/0 = 0
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem B.3, p.60, citing [New64] and [PP87, Section 4.1]

import Mathlib
import Definitions.Def_SigmoidWire_RatApproxOn

namespace SigmoidWire

/-- **Theorem B.3 (Newman's theorem).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem B.3, p.60 (PDF p.62),
citing [New64] and [PP87, Section 4.1]: "There is an absolute constant C_N such that for every
integer n ≥ 1, there is a rational function N_n of degree at most n with |N_n(y) − |y|| ≤ C_N e^{−√n}
for all y ∈ [−1, 1]."

**Formalization Note.** `RatApproxOn g 1 n err` asks for real polynomials `P, Q` of degree at most
`n` with `Q ≠ 0` on `[−1, 1]` (the inequality "for all y ∈ [−1, 1]" presupposes that `N_n` is
defined there) and `|P/Q − |·|| ≤ err` on `[−1, 1]`. -/
theorem theorem_B_3 :
    ∃ CN : ℝ, ∀ n : ℕ, 1 ≤ n →
      RatApproxOn (fun y => |y|) 1 n (CN * Real.exp (-Real.sqrt n)) := by sorry

end SigmoidWire

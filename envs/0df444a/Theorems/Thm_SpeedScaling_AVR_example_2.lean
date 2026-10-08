-- Prove2me | Theorems.Thm_SpeedScaling_AVR_example_2
-- name    : SpeedScaling.AVR.example_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:05.449717+00:00
-- url     : https://prove2.me/theorems/b0d20e4b-6443-4019-801a-5da742d4426f
-- title:
--   Example 2 — ratios two and four and the exponent maximum
-- statement:
--   In Example 2, the displayed slot schedule is optimal for every exponent $e\ge1$ and positive $n$. The AVR-to-optimal-energy ratio tends to two for $e=1$ and to four for $e=3/2$. For every $e\ge1$, its eventual ratio is at most every constant above four, so the limiting maximum is four.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 376, Example 2.

import Definitions.Def_SpeedScaling_AVR_Example2

namespace SpeedScaling.AVR
open Filter

theorem example_2 :
    (∀ (e : ℝ), 1 ≤ e → ∀ n : ℕ, ∀ hn : 0 < n,
      IsOptimal (fun x : ℝ => x ^ 2)
        (ex2InstancePower e n hn) (ex2SchedulePower e n hn)) ∧
    Tendsto (fun n : ℕ =>
      AVR (ex2InstancePower 1 (n + 1) (Nat.zero_lt_succ n)) /
      energy (fun x : ℝ => x ^ 2)
        (ex2InstancePower 1 (n + 1) (Nat.zero_lt_succ n))
        (ex2SchedulePower 1 (n + 1) (Nat.zero_lt_succ n)))
      atTop (nhds (2 : ℝ)) ∧
    Tendsto (fun n : ℕ =>
      AVR (ex2Instance (n + 1) (Nat.zero_lt_succ n)) /
      energy (fun x : ℝ => x ^ 2)
        (ex2Instance (n + 1) (Nat.zero_lt_succ n))
        (ex2Schedule (n + 1) (Nat.zero_lt_succ n)))
      atTop (nhds (4 : ℝ)) ∧
    (∀ (e c : ℝ), 1 ≤ e → 4 < c → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      AVR (ex2InstancePower e (n + 1) (Nat.zero_lt_succ n)) /
        energy (fun x : ℝ => x ^ 2)
          (ex2InstancePower e (n + 1) (Nat.zero_lt_succ n))
          (ex2SchedulePower e (n + 1) (Nat.zero_lt_succ n)) ≤ c) := by sorry

end SpeedScaling.AVR

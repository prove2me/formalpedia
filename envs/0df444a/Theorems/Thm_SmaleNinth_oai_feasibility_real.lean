-- Prove2me | Theorems.Thm_SmaleNinth_oai_feasibility_real
-- name    : SmaleNinth.oai_feasibility_real
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-26T02:48:50.38072+00:00
-- url     : https://prove2.me/theorems/c111cba8-1c62-4bb6-9203-e9ad85618c0e
-- title:
--   Strongly polynomial LP feasibility over $\mathbb{R}$ (OpenAI RAM model)
-- statement:
--   There exist a program $p$ of OpenAI's random-access machine (data registers over the scalar field, natural-number address registers, rational constants, the four field operations, comparisons and indirect addressing) and constants $c, e \in \mathbb{N}$ such that for all $m, d \ge 1$, every matrix $A \in \mathbb{R}^{m \times d}$ and every $b \in \mathbb{R}^m$, the run of $p$ on the input tape $(A \text{ by rows}, b)$ with dimensions $m, d$ in the first two address registers halts after $k$ steps with
--   $$k \le c\,(m+d+1)^e,$$
--   and its final state either carries tag $0$ and a point $x \in \mathbb{R}^d$ with $Ax \le b$, or carries tag $1$ and a Farkas certificate $y \in \mathbb{R}^m$ with $y \ge 0$, $A^{\mathsf T} y = 0$, $b^{\mathsf T} y < 0$ and at most $\operatorname{rank} A + 1$ nonzero entries.
--
--   **Role.** This is OpenAI's strongly polynomial feasibility theorem with the scalar field $\mathbb{Q}$ replaced by $\mathbb{R}$ (the rational bit-size bound has no meaning over $\mathbb{R}$ and is dropped). The rational case is proved on the platform as `OAI.Optimization.LinearProgramming.strongly_polynomial_feasibility`; the preprint claims the real case (Theorem 1, §3.4), but its Lean development proves only the rational one. Together with `SmaleNinth.real_ram_of_oai_program` it implies `SmaleNinth.smale_ninth_real_ram`, hence Smale's ninth problem. It is the remaining open core of the mission.
-- source:
--   OpenAI, *Strongly polynomial linear programming* (preprint, Nov 2026), https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6 — Lean: OAI/Optimization/LinearProgramming/Specification.lean (StronglyPolynomialFeasibility) and Feasibility.lean. Real-data claim: Theorem 1 and §3.4 (ordered fields) of the preprint.

import Definitions.Def_OAILP_Specification
import Mathlib.Data.Real.Basic

open OAI.Optimization.LinearProgramming

theorem SmaleNinth.oai_feasibility_real :
    ∃ (p : RAM.Program) (c e : ℕ), ∀ (m d : ℕ), 0 < m → 0 < d →
      ∀ (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ),
      ∃ (k : ℕ) (t : Fin (k + 1) → RAM.State ℝ),
        RAM.Trace p (RAM.start [m, d] (lpInput A b)) k t ∧ k ≤ RAM.polyBound c e (m + d) ∧
        FeasibilityOutput A b (t (Fin.last k)) := by sorry

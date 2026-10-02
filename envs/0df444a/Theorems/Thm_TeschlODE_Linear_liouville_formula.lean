-- Prove2me | Theorems.Thm_TeschlODE_Linear_liouville_formula
-- name    : TeschlODE.Linear.liouville_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:56:40.39419+00:00
-- url     : https://prove2.me/theorems/4fd12211-328f-4a7e-b1d8-f03a4925e73e
-- title:
--   Lemma 3.11 — Liouville's formula (Abel's identity) for the Wronski determinant
-- statement:
--   Let $I$ be an interval, $A \in C(I, \mathbb{R}^{n\times n})$, and let $U(t) = (\varphi_1(t), \dots, \varphi_n(t))$ be a matrix whose columns are solutions of $\dot x = A(t)x$ on $I$. Then the Wronski determinant $W(t) = \det U(t)$ satisfies
--   $$W(t) = W(t_0)\,\exp\Big(\int_{t_0}^{t} \operatorname{tr}(A(s))\,ds\Big), \qquad t_0, t \in I. \qquad (3.91)$$
--
--   In particular $\det U(t) \neq 0$ at one point of $I$ implies it at every point, and for periodic $A$ the determinant of the monodromy matrix is $\exp\big(\int_0^T \operatorname{tr} A\big) > 0$ (3.122), which is what makes a matrix logarithm of it available in Floquet's theorem.
--
--   **Formalization Note.** The book writes $U$ with the solutions as columns ("using the solutions as columns", (3.81)); the Lean hypothesis is that each column `fun t i => U t i j` is an `IsSolution A I`. The integral is the interval integral `∫ s in t₀..t`, which is oriented (so $t < t_0$ is allowed) and is a genuine integral because $\operatorname{tr} A$ is continuous on $[t_0,t] \subseteq I$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 83, Lemma 3.11

import Mathlib
import Definitions.Def_TeschlODE_Linear_IsSolution

namespace TeschlODE.Linear

/-- Teschl, Lemma 3.11 (p. 83), Abel's identity / Liouville's formula (3.91): if the columns of
`U(t)` are `n` solutions of (3.79) on the interval `I`, the Wronski determinant
`W(t) = det U(t)` satisfies `W(t) = W(t₀) exp (∫_{t₀}^{t} tr A(s) ds)` for all `t₀, t ∈ I`. -/
theorem liouville_formula {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (I : Set ℝ)
    (hI : I.OrdConnected) (hA : ContinuousOn A I) (U : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hU : ∀ j : Fin n, IsSolution A I (fun t i => U t i j)) (t₀ t : ℝ) (ht₀ : t₀ ∈ I)
    (ht : t ∈ I) :
    (U t).det = (U t₀).det * Real.exp (∫ s in t₀..t, (A s).trace) := by sorry

end TeschlODE.Linear

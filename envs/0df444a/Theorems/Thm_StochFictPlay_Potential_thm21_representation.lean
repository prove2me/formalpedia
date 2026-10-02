-- Prove2me | Theorems.Thm_StochFictPlay_Potential_thm21_representation
-- name    : StochFictPlay.Potential.thm21_representation
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-28T10:09:59.851741+00:00
-- url     : https://prove2.me/theorems/22cd2221-bb4f-4dea-aba2-5b645f20c488
-- title:
--   Theorem 2.1 — every additive random utility choice function has an admissible deterministic perturbation representation
-- statement:
--   Let $m \ge 1$ and let $\varepsilon$ be a random vector in $\mathbb R^m$ with a strictly positive density $f$ such that the choice function
--   $$C_i(\pi) = P\big(\operatorname*{arg\,max}_j\ \pi_j + \varepsilon_j = i\big)$$
--   is continuously differentiable. Then there is an admissible deterministic perturbation $V$ such that for every payoff vector $\pi \in \mathbb R^m$,
--   $$C(\pi) = \operatorname*{arg\,max}_{y \in \operatorname{int}(\Delta)} \big(y\cdot\pi - V(y)\big),$$
--   the maximizer being unique.
--
--   In this mission the theorem is the bridge from the stochastically perturbed dynamic (P) to the deterministically perturbed dynamic (PV): with $\tilde C^\alpha = C^\alpha$, the fields of (P) and (PV) coincide, so Propositions 4.1–4.3 apply to (P).
--
--   **Formalization Note** One $V$ serves all $\pi$. The argmax is expressed as: $C(\pi)$ lies in $\operatorname{int}(\Delta)$ and strictly beats every other interior point. This restates the goal of mission I of this series in this mission's definitions.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 5, Theorem 2.1

import Mathlib
import Definitions.Def_StochFictPlay_Potential_ChoiceModel

open MeasureTheory
open scoped ENNReal

namespace StochFictPlay.Potential

/-- Theorem 2.1 (Hofbauer–Sandholm 2002, manuscript p. 5), restated for this mission: if the
shock vector has a strictly positive density `f` on `ℝ^m` and the choice function
`C = choiceProb f` is continuously differentiable, there is one admissible deterministic
perturbation `V` (independent of `π`) with `C(π) = argmax_{y ∈ int(∆A)} (y · π − V(y))` for
every `π`, the argmax being unique. -/
theorem thm21_representation (m : ℕ) (hm : 1 ≤ m) (f : (Fin m → ℝ) → ℝ≥0∞)
    (hf : IsRegularDensity f) :
    ∃ V : (Fin m → ℝ) → ℝ, IsAdmissible V ∧ IsPerturbedArgmax V (choiceProb f) := by sorry

end StochFictPlay.Potential

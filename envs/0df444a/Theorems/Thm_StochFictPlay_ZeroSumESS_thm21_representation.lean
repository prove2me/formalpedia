-- Prove2me | Theorems.Thm_StochFictPlay_ZeroSumESS_thm21_representation
-- name    : StochFictPlay.ZeroSumESS.thm21_representation
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-28T09:40:57.690716+00:00
-- url     : https://prove2.me/theorems/0752bd73-0e4c-4938-a047-78eee89a8a73
-- title:
--   Theorem 2.1 — every additive random utility choice function has an admissible deterministic perturbation representation
-- statement:
--   Let $m \ge 1$ and let the random vector $\varepsilon$ have a strictly positive density $f$ on $\mathbb R^m$ such that the choice function $C_i(\pi) = P(\operatorname{argmax}_j \pi_j + \varepsilon_j = i)$ is continuously differentiable. Then there is an admissible deterministic perturbation $V : \operatorname{int}(\Delta) \to \mathbb R$ such that for every payoff vector $\pi \in \mathbb R^m$
--   $$C(\pi) = \operatorname*{arg\,max}_{y \in \operatorname{int}(\Delta)} \big(y\cdot\pi - V(y)\big),$$
--   the maximizer being unique.
--
--   This is the representation that §4 uses to replace the perturbed best response dynamics (P) and (SP) by the deterministically perturbed dynamics (PV) and (SPV).
--
--   **Formalization Note** This restates, with this mission's definitions, the goal of mission I of the series; drafts cannot import each other. One $V$ serves every $\pi$.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 5, Theorem 2.1

import Mathlib
import Definitions.Def_StochFictPlay_ZeroSumESS_ChoiceModel

open MeasureTheory
open scoped ENNReal

namespace StochFictPlay.ZeroSumESS

/-- Theorem 2.1 (Hofbauer–Sandholm 2002, manuscript p. 5), restated for this mission: if the
shock vector has a strictly positive density `f` on `ℝ^m` and the choice function
`C = choiceProb f` is continuously differentiable, there is one admissible deterministic
perturbation `V` (independent of `π`) with `C(π) = argmax_{y ∈ int(∆A)} (y · π − V(y))` for
every `π`, the argmax being unique. -/
theorem thm21_representation (m : ℕ) (hm : 1 ≤ m) (f : (Fin m → ℝ) → ℝ≥0∞)
    (hf : IsRegularDensity f) :
    ∃ V : (Fin m → ℝ) → ℝ, IsAdmissible V ∧ IsPerturbedArgmax V (choiceProb f) := by sorry

end StochFictPlay.ZeroSumESS

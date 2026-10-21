-- Prove2me | Theorems.Thm_QuickestOU_Detection_proposition_8
-- name    : QuickestOU.Detection.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:44.971655+00:00
-- url     : https://prove2.me/theorems/7aca7a7f-5aa9-4613-b9eb-64a2848ba180
-- title:
--   Proposition 8 — stopping boundary is finite at every x
-- statement:
--   For every initial observation $x\in\mathbb R$, the stopping set has a point above that observation:
--
--   $$\forall x\in\mathbb R\;\exists\varphi\ge0:\widehat V(\varphi,x)=0.$$
--
--   Consequently the stopping threshold $b(x)$ is finite at each $x$. This existence statement is the substantive content of Proposition 8 when the boundary is represented by a real infimum.
--
--   **Formalization Note** The result rules out an empty fibre, for which Lean's real infimum would otherwise return zero.
-- source:
--   Glover & Peskir, Quickest detection problems for Ornstein–Uhlenbeck processes, Research Report No. 11 (2017, revised), Probab. Statist. Group Manchester; to appear in Math. Oper. Res.; https://doi.org/10.1287/moor.2021.0186; p. 21, Proposition 8

import Mathlib
import Definitions.Def_QuickestOU_Detection_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuickestOU.Detection

/-- Proposition 8: every x-fibre of the stopping set is nonempty. -/
theorem proposition_8 (P : Params) (hS : P.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (hB : Driver μ B) :
    ∀ x : ℝ, ∃ phi : ℝ, 0 ≤ phi ∧ Vhat P B μ hB.meas phi x = 0 := by sorry

end QuickestOU.Detection

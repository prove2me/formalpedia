-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_gamma
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_gamma
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:54.242593+00:00
-- url     : https://prove2.me/theorems/a54ab15d-a5e1-4dae-8128-c7be336669d3
-- title:
--   Geometry Of Numbers Theory: sph Monom gamma
-- statement:
--   The Geometry Of Numbers Theory construction uses the sph Monom gamma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L218-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L218-L223

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
variable {N : ℕ}

theorem ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_gamma (D n k : ℕ) (h : k = n + n) :
    Real.Gamma ((((2 * (D + 1) - 1 + k : ℕ) : ℝ) + 1) / 2) = ((D + n).factorial : ℝ) := by sorry

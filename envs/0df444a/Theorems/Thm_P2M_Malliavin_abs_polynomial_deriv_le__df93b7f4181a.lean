-- Prove2me | Theorems.Thm_P2M_Malliavin_abs_polynomial_deriv_le__df93b7f4181a
-- name    : P2M_Malliavin_abs_polynomial_deriv_le__df93b7f4181a
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:16:48.457806+00:00
-- url     : https://prove2.me/theorems/4921ab2b-9199-5f6c-ba55-7133226a6af2
-- title:
--   P2 M Malliavin abs polynomial deriv le  df93b7f4181a: P2 M Malliavin abs polynomial deriv le  df93b7f4181a
-- statement:
--   The P2 M Malliavin abs polynomial deriv le  df93b7f4181a construction uses the P2 M Malliavin abs polynomial deriv le  df93b7f4181a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L609-L614
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L609-L614

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {g : ℝ → ℝ}

theorem P2M_Malliavin_abs_polynomial_deriv_le__df93b7f4181a (p : Polynomial ℝ) (x : ℝ) :
    |deriv (fun x ↦ p.eval x) x| ≤
      (coeffMass p + coeffMass p.derivative) * Real.exp (p.natDegree * |x|) := by sorry

alias «Malliavin».«abs_polynomial_deriv_le'» := P2M_Malliavin_abs_polynomial_deriv_le__df93b7f4181a

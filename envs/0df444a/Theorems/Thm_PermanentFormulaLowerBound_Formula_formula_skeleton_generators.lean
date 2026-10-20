-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_Formula_formula_skeleton_generators
-- name    : PermanentFormulaLowerBound.Formula.formula_skeleton_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/07cfbb44-e3d7-4987-83c2-44cff684d811
-- title:
--   PermanentFormulaLowerBound.Formula.formula_skeleton_generators
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
variable {Y : Type u} {Z : Type v} {F : Type w}
variable [Field F]

theorem PermanentFormulaLowerBound.Formula.formula_skeleton_generators
    (f : Formula (Y ⊕ Z) F) (hmarked : 0 < yLeafCount f) :
    ∃ s : Finset (FractionRing (MvPolynomial Z F)),
      s.card ≤ 4 * yLeafCount f - 2 ∧
        ∀ α : Y →₀ ℕ,
          algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
            (MvPolynomial.coeff α (splitEval f)) ∈
              IntermediateField.adjoin F (s : Set _) := by sorry

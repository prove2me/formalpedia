-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CGlue_arith
-- name    : PositivityTheory.Rg.Cz.CGlue.arith
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:47:59.406945+00:00
-- url     : https://prove2.me/theorems/b461a481-fb7c-47f8-8399-35764bddd005
-- title:
--   CGlue: arith
-- statement:
--   The CGlue construction uses the arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L111-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L111-L130

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CoefficientGluing_SumFinVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Formalism.REAL
open scoped TensorProduct
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CGlue

theorem PositivityTheory.Rg.Cz.CGlue.arith (n : ℕ) (s : ℤ) (ν : Fin n → ℕ) (l : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (h : ∀ i, s - l (w i) = (ν i : ℤ) + (i : ℕ)) :
    (∑ i, (ν i : ℝ) * ((ν i : ℝ) + 2 * (i : ℕ) + 1 - n)) - (2 * s * ∑ i, (ν i : ℝ) - n * (s : ℝ) ^ 2) =
      ∑ k, (((l k : ℝ) + ((n : ℝ) - 1) / 2) ^ 2 - (((n : ℝ) - 1) / 2 - (k : ℕ)) ^ 2) := by sorry

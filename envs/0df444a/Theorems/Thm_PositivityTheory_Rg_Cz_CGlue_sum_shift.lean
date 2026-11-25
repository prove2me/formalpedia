-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CGlue_sum_shift
-- name    : PositivityTheory.Rg.Cz.CGlue.sum_shift
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:11.394882+00:00
-- url     : https://prove2.me/theorems/1bbaa3d3-a366-4211-9396-19766335930e
-- title:
--   CGlue: sum shift
-- statement:
--   The CGlue construction uses the sum shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L132-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L132-L142

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

theorem PositivityTheory.Rg.Cz.CGlue.sum_shift (n : ℕ) (s : ℤ) (ν : Fin n → ℕ) (l : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (h : ∀ i, s - l (w i) = (ν i : ℤ) + (i : ℕ)) :
    ∑ k, ((l k : ℝ) + (k : ℕ)) = n * s - ∑ i, (ν i : ℝ) := by sorry

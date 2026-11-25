-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CGlue_sum_fin_val
-- name    : PositivityTheory.Rg.Cz.CGlue.sum_fin_val
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:04.54485+00:00
-- url     : https://prove2.me/theorems/ccf96416-d8c4-4061-a309-997369f9a564
-- title:
--   CGlue: sum fin val
-- statement:
--   The CGlue construction uses the sum fin val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L101-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L101-L109

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

theorem PositivityTheory.Rg.Cz.CGlue.sum_fin_val (n : ℕ) : (∑ i : Fin n, ((i : ℕ) : ℝ)) * 2 = n * (n - 1) := by sorry

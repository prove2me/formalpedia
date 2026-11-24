-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CGlue_tE_diag_sum
-- name    : PositivityTheory.Rg.Cz.CGlue.tE_diag_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:10.29781+00:00
-- url     : https://prove2.me/theorems/018b204e-dffd-410e-b357-9adf2d788c12
-- title:
--   CGlue: t E diag sum
-- statement:
--   The CGlue construction uses the t E diag sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L19-L31

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
variable {n : ℕ} {P : Type} [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.CGlue.tE_diag_sum (S : Finset P) (f : TV n ℂ P) :
    ∑ i, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) i i f = (S.card : ℂ) • f := by sorry

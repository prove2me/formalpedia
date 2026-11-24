-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CGlue_tmap_apply
-- name    : PositivityTheory.Rg.Cz.CGlue.tmap_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:09.008544+00:00
-- url     : https://prove2.me/theorems/01264ec6-853c-44d9-8265-4737fde87605
-- title:
--   CGlue: tmap apply
-- statement:
--   The CGlue construction uses the tmap apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L61-L63

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
variable {M : Type} [AddCommGroup M] [Module ℂ M] {d : ℕ}

theorem PositivityTheory.Rg.Cz.CGlue.tmap_apply (Jh : Matrix (Fin d) (P → Fin n) ℂ) (f : TV n M P) :
    tmap Jh f = ∑ I, f I ⊗ₜ (fun m => Jh m I) := by sorry

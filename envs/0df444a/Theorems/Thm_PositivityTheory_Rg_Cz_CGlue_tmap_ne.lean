-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CGlue_tmap_ne
-- name    : PositivityTheory.Rg.Cz.CGlue.tmap_ne
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:47:57.106955+00:00
-- url     : https://prove2.me/theorems/e10705ff-a4eb-448f-b5c4-44abf7745705
-- title:
--   CGlue: tmap ne
-- statement:
--   The CGlue construction uses the tmap ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L86-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L86-L97

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

theorem PositivityTheory.Rg.Cz.CGlue.tmap_ne (Jh : Matrix (Fin d) (P → Fin n) ℂ) (f : TV n M P) (lam : M →ₗ[ℂ] ℂ)
    (h : Jh *ᵥ (fun I => lam (f I)) ≠ 0) : tmap Jh f ≠ 0 := by sorry

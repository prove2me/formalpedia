-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CGlue_cas_shift
-- name    : PositivityTheory.Rg.Cz.CGlue.cas_shift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:00.788855+00:00
-- url     : https://prove2.me/theorems/78f90632-7fac-4c8c-97e8-2177ce105fd4
-- title:
--   CGlue: cas shift
-- statement:
--   The CGlue construction uses the cas shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L33-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L33-L48

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

theorem PositivityTheory.Rg.Cz.CGlue.cas_shift (S : Finset P) (s : ℂ) (f : TV n ℂ P) :
    ∑ i, ∑ j, (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) i j
        (tE S 0 j i f - if j = i then s • f else 0) - if i = j then s • (tE S 0 j i f - if j = i then s • f else 0) else 0) =
      (∑ a, ∑ c, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c * tE S 0 c a : Module.End ℂ (TV n ℂ P)) f -
        (2 * s * S.card - n * s ^ 2) • f := by sorry

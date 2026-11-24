-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TA_tE_empty
-- name    : PositivityTheory.Rg.Cz.TA.tE_empty
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:31.593134+00:00
-- url     : https://prove2.me/theorems/b61aacf3-389a-4678-b9bc-cafd0e0f7456
-- title:
--   TA: t E empty
-- statement:
--   The TA construction uses the t E empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L62-L65

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P : Type} [Fintype P] [DecidableEq P]
omit [Fintype P]

theorem PositivityTheory.Rg.Cz.TA.tE_empty (F : Fin n → Fin n → Module.End ℂ M) :
    (tE (∅ : Finset P) F : Fin n → Fin n → Module.End ℂ (TV n M P)) = fun a b => lift (F a b) := by sorry

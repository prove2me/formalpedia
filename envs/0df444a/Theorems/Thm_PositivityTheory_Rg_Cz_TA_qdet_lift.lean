-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TA_qdet_lift
-- name    : PositivityTheory.Rg.Cz.TA.qdet_lift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:08.70212+00:00
-- url     : https://prove2.me/theorems/e0e0bfec-42f8-423c-93cb-14eedeb5f515
-- title:
--   TA: qdet lift
-- statement:
--   The TA construction uses the qdet lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L53-L59

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
omit [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TA.qdet_lift (F : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℂ) (h : HasChar F l) :
    HasChar (fun a b => (lift (F a b) : Module.End ℂ (TV n M P))) l := by sorry

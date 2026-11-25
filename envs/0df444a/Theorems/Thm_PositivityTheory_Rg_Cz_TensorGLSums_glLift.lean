-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TensorGLSums_glLift
-- name    : PositivityTheory.Rg.Cz.TensorGLSums.glLift
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:43.819283+00:00
-- url     : https://prove2.me/theorems/6ba68bf9-39a8-49e1-ac02-6202a018adf7
-- title:
--   Tensor GLSums: gl Lift
-- statement:
--   The Tensor GLSums construction uses the gl Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGl.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGl.lean#L96-L101

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGl
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TensorGLSums
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [DecidableEq P]
omit [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TensorGLSums.glLift (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) :
    GlRel (fun a b => (lift (E a b) : Module.End ℂ (TV n M P))) := by sorry

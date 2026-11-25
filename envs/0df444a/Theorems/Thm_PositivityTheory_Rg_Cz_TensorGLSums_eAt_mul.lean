-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TensorGLSums_eAt_mul
-- name    : PositivityTheory.Rg.Cz.TensorGLSums.eAt_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:54:45.883514+00:00
-- url     : https://prove2.me/theorems/74d14dfd-dbe8-5577-8391-37f83c9d5e67
-- title:
--   Tensor GLSums: e At mul
-- statement:
--   The Tensor GLSums construction uses the e At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGl.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGl.lean#L73-L79

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

theorem PositivityTheory.Rg.Cz.TensorGLSums.eAt_mul (p : P) (a b c d : Fin n) :
    (eAt p a b * eAt p c d : Module.End ℂ (TV n M P)) = if b = c then eAt p a d else 0 := by sorry

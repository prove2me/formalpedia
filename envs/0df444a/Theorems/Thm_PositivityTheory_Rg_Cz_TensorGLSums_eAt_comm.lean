-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TensorGLSums_eAt_comm
-- name    : PositivityTheory.Rg.Cz.TensorGLSums.eAt_comm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:32.645016+00:00
-- url     : https://prove2.me/theorems/f1a71bdc-65cf-45df-8bf5-ac46557f5cd6
-- title:
--   Tensor GLSums: e At comm
-- statement:
--   The Tensor GLSums construction uses the e At comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGl.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGl.lean#L81-L86

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

theorem PositivityTheory.Rg.Cz.TensorGLSums.eAt_comm {p q : P} (h : p ≠ q) (a b c d : Fin n) :
    (eAt p a b * eAt q c d : Module.End ℂ (TV n M P)) = eAt q c d * eAt p a b := by sorry

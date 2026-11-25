-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_cl_all
-- name    : PositivityTheory.Rg.Cz.SpecA.cl_all
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:53:35.669985+00:00
-- url     : https://prove2.me/theorems/9b05414c-a57e-547d-a966-464f199a0348
-- title:
--   Spec A: cl all
-- statement:
--   The Spec A construction uses the cl all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L284-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L284-L292

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SpecA
variable {n : ℕ}

theorem PositivityTheory.Rg.Cz.SpecA.cl_all (h1 : TensorGl) (h3 : Curry) (h5 : StepChar) : ∀ m, Cl m := by sorry

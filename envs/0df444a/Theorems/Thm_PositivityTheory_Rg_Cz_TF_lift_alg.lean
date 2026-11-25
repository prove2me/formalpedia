-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TF_lift_alg
-- name    : PositivityTheory.Rg.Cz.TF.lift_alg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:08.720549+00:00
-- url     : https://prove2.me/theorems/eed1f7ee-3e7f-487c-8f36-96e41c7ec517
-- title:
--   TF: lift alg
-- statement:
--   The TF construction uses the lift alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFin.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFin.lean#L34-L37

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFin
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
open PositivityTheory.Rg.Cz.TF

theorem PositivityTheory.Rg.Cz.TF.lift_alg {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} (c : ℂ) :
    (lift (algebraMap ℂ (Module.End ℂ M) c) : Module.End ℂ (TV n M P)) = algebraMap ℂ _ c := by sorry

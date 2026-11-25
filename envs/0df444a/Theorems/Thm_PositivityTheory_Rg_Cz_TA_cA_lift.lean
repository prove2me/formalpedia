-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TA_cA_lift
-- name    : PositivityTheory.Rg.Cz.TA.cA_lift
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:22.906439+00:00
-- url     : https://prove2.me/theorems/f287e90a-96d5-55cb-8f97-d4c7f2f445ea
-- title:
--   TA: c A lift
-- statement:
--   The TA construction uses the c A lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L80-L83

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

theorem PositivityTheory.Rg.Cz.TA.cA_lift {C : Type} [DecidableEq C] (col : P → C) (b : P → Fin n) (B : Module.End ℂ M) :
    cA col b ∘ₗ lift B = B ∘ₗ (cA col b : TV n M P →ₗ[ℂ] M) := by sorry

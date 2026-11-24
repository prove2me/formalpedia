-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_lift_comm_pm
-- name    : PositivityTheory.Rg.Cz.lift_comm_pm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:42.216397+00:00
-- url     : https://prove2.me/theorems/9ff96bdb-b33c-4824-86fc-c6c58d57b12e
-- title:
--   Cz: lift comm pm
-- statement:
--   The Cz construction uses the lift comm pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L49-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L49-L49

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
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
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
omit [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.lift_comm_pm (B : Module.End ℂ M) (σ : Equiv.Perm P) : Commute (lift B : Module.End ℂ (TV n M P)) (pm σ) := by sorry

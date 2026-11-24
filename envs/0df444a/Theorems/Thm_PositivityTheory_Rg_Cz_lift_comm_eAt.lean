-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_lift_comm_eAt
-- name    : PositivityTheory.Rg.Cz.lift_comm_eAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:22.8292+00:00
-- url     : https://prove2.me/theorems/12ab1aae-3f48-4725-8f57-ca61c63c633b
-- title:
--   Cz: lift comm e At
-- statement:
--   The Cz construction uses the lift comm e At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L60-L63

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
omit [Fintype P]

theorem PositivityTheory.Rg.Cz.lift_comm_eAt (B : Module.End ℂ M) (p : P) (a b : Fin n) : Commute (lift B) (eAt p a b) := by sorry

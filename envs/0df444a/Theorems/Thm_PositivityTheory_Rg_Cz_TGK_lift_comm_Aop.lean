-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_lift_comm_Aop
-- name    : PositivityTheory.Rg.Cz.TGK.lift_comm_Aop
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:35.614027+00:00
-- url     : https://prove2.me/theorems/b658b7c8-f6eb-4c69-8838-b775d2f38c26
-- title:
--   TGK: lift comm Aop
-- statement:
--   The TGK construction uses the lift comm Aop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L31-L33

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TGK.lift_comm_Aop (B : Module.End ℂ M) (K : P → Matrix (Fin n) (Fin n) ℂ) : Commute (lift B) (Aop K) := by sorry

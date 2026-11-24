-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
-- name    : PositivityTheory.Rg.Cz.lift_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:47.533424+00:00
-- url     : https://prove2.me/theorems/2dee48ba-ddd7-4fd0-a446-dd7b90b44842
-- title:
--   Cz: lift apply
-- statement:
--   The Cz construction uses the lift apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L12-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L12-L12

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

theorem PositivityTheory.Rg.Cz.lift_apply (B : Module.End ℂ M) (f : TV n M P) (I : P → Fin n) : lift B f I = B (f I) := by sorry

attribute [defeq] PositivityTheory.Rg.Cz.lift_apply

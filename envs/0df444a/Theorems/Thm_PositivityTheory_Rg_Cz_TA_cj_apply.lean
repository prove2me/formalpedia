-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TA_cj_apply
-- name    : PositivityTheory.Rg.Cz.TA.cj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:33.79881+00:00
-- url     : https://prove2.me/theorems/0db63fc0-cac1-4dca-868a-104370c243d6
-- title:
--   TA: cj apply
-- statement:
--   The TA construction uses the cj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L94-L95

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

theorem PositivityTheory.Rg.Cz.TA.cj_apply {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (X : Module.End ℂ W) (v : V) : cj e X v = e.symm (X (e v)) := by sorry

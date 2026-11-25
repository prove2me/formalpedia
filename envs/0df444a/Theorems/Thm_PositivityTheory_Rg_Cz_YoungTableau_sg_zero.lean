-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_sg_zero
-- name    : PositivityTheory.Rg.Cz.YoungTableau.sg_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:49:13.650694+00:00
-- url     : https://prove2.me/theorems/12ead1e4-4a73-4dda-9f49-bb8147aaf578
-- title:
--   Young Tableau: sg zero
-- statement:
--   The Young Tableau construction uses the sg zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungA.lean#L239-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungA.lean#L239-L244

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA
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
open PositivityTheory.Rg.Cz.YoungTableau
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {X : Type} [Fintype X] [DecidableEq X]
  {C : Type} [DecidableEq C]

theorem PositivityTheory.Rg.Cz.YoungTableau.sg_zero (col : X → C) (b : X → Fin n) (v : X → Fin n) (h : ¬ ∃ π ∈ colG col, b ∘ π = v) :
    sg col b v = 0 := by sorry

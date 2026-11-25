-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_sg_perm
-- name    : PositivityTheory.Rg.Cz.YoungTableau.sg_perm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:48:55.424598+00:00
-- url     : https://prove2.me/theorems/ba7b76bf-8cd1-464c-ad9f-1f83b075d2f2
-- title:
--   Young Tableau: sg perm
-- statement:
--   The Young Tableau construction uses the sg perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungA.lean#L223-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungA.lean#L223-L237

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

theorem PositivityTheory.Rg.Cz.YoungTableau.sg_perm (col : X → C) (b : X → Fin n) (hI : ColInj col b) (π : Equiv.Perm X) (hπ : π ∈ colG col) :
    sg col b (b ∘ π) = Equiv.Perm.sign π := by sorry

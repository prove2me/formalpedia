-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_mem_colG
-- name    : PositivityTheory.Rg.Cz.YoungTableau.mem_colG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:36.940805+00:00
-- url     : https://prove2.me/theorems/b461bac0-d83c-4a75-8534-0bd9d2dc2f0b
-- title:
--   Young Tableau: mem col G
-- statement:
--   The Young Tableau construction uses the mem col G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungA.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungA.lean#L18-L19

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

theorem PositivityTheory.Rg.Cz.YoungTableau.mem_colG (col : X → C) (π : Equiv.Perm X) : π ∈ colG col ↔ ∀ p, col (π p) = col p := by sorry

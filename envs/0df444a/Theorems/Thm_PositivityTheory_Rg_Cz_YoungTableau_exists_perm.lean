-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_exists_perm
-- name    : PositivityTheory.Rg.Cz.YoungTableau.exists_perm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:49:16.1978+00:00
-- url     : https://prove2.me/theorems/4edd17ae-c6f0-51d3-8c7f-9bb538ea262f
-- title:
--   Young Tableau: exists perm
-- statement:
--   The Young Tableau construction uses the exists perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungA.lean#L116-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungA.lean#L116-L218

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

theorem PositivityTheory.Rg.Cz.YoungTableau.exists_perm (col : X → C) (b : X → Fin n) (hT : IsTab col b) (ζ : Equiv.Perm X)
    (hJ : ColInj col (b ∘ ζ)) : ∃ π ∈ colG col, b ∘ π = b ∘ ζ := by sorry

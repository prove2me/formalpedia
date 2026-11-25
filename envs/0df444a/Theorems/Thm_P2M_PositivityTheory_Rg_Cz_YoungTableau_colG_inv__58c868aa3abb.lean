-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Cz_YoungTableau_colG_inv__58c868aa3abb
-- name    : P2M_PositivityTheory_Rg_Cz_YoungTableau_colG_inv__58c868aa3abb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:10:15.749732+00:00
-- url     : https://prove2.me/theorems/748d1f66-1041-4e34-9dac-8af49c71c15b
-- title:
--   P2 M Positivity Theory Rg Cz Young Tableau col G inv  58c868aa3abb: P2 M Positivity Theory Rg Cz Young Tableau col G inv  58c868aa3abb
-- statement:
--   The P2 M Positivity Theory Rg Cz Young Tableau col G inv  58c868aa3abb construction uses the P2 M Positivity Theory Rg Cz Young Tableau col G inv  58c868aa3abb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungB.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungB.lean#L22-L26

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungB
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
variable {n N : ℕ} {ι : Type} [DecidableEq ι] {C : Type} [DecidableEq C]

theorem P2M_PositivityTheory_Rg_Cz_YoungTableau_colG_inv__58c868aa3abb {X : Type} [Fintype X] [DecidableEq X] {D : Type} [DecidableEq D] (col : X → D)
    {π : Equiv.Perm X} (h : π ∈ colG col) : π⁻¹ ∈ colG col := by sorry

alias «PositivityTheory».«Rg».«Cz».«YoungTableau».«colG_inv'» := P2M_PositivityTheory_Rg_Cz_YoungTableau_colG_inv__58c868aa3abb

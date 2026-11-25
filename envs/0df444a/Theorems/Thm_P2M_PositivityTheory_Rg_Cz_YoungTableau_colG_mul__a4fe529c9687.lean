-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Cz_YoungTableau_colG_mul__a4fe529c9687
-- name    : P2M_PositivityTheory_Rg_Cz_YoungTableau_colG_mul__a4fe529c9687
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:10:32.861619+00:00
-- url     : https://prove2.me/theorems/2e535369-2613-438e-b57f-8752dcc68a79
-- title:
--   P2 M Positivity Theory Rg Cz Young Tableau col G mul  a4fe529c9687: P2 M Positivity Theory Rg Cz Young Tableau col G mul  a4fe529c9687
-- statement:
--   The P2 M Positivity Theory Rg Cz Young Tableau col G mul  a4fe529c9687 construction uses the P2 M Positivity Theory Rg Cz Young Tableau col G mul  a4fe529c9687 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungB.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungB.lean#L18-L20

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

theorem P2M_PositivityTheory_Rg_Cz_YoungTableau_colG_mul__a4fe529c9687 {X : Type} [Fintype X] [DecidableEq X] {D : Type} [DecidableEq D] (col : X → D)
    {π π' : Equiv.Perm X} (h : π ∈ colG col) (h' : π' ∈ colG col) : π * π' ∈ colG col := by sorry

alias «PositivityTheory».«Rg».«Cz».«YoungTableau».«colG_mul'» := P2M_PositivityTheory_Rg_Cz_YoungTableau_colG_mul__a4fe529c9687

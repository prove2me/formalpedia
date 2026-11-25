-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_deg_xJ
-- name    : PositivityTheory.Rg.Cz.ColumnAntisymmetry.deg_xJ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:48:53.084112+00:00
-- url     : https://prove2.me/theorems/9246f814-433d-44ba-853d-932c9455af2e
-- title:
--   Column Antisymmetry: deg x J
-- statement:
--   The Column Antisymmetry construction uses the deg x J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiA.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiA.lean#L45-L51

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
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
open PositivityTheory.Rg.Cz.ColumnAntisymmetry
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {m : ℕ} {E : Fin n → Fin n → Module.End ℂ M}

theorem PositivityTheory.Rg.Cz.ColumnAntisymmetry.deg_xJ (j : Fin m) : Deg E 1 (xJ E j) := by sorry

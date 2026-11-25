-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_npairs_eq
-- name    : PositivityTheory.Rg.Cz.ColumnAntisymmetry.npairs_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:48:55.803578+00:00
-- url     : https://prove2.me/theorems/d39f9d6f-13ee-4ccc-8513-2ebda5783b2d
-- title:
--   Column Antisymmetry: npairs eq
-- statement:
--   The Column Antisymmetry construction uses the npairs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiA.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiA.lean#L73-L76

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

theorem PositivityTheory.Rg.Cz.ColumnAntisymmetry.npairs_eq (col : Fin m → ℕ) :
    (∑ j : Fin m, ∑ i : Fin m, if i < j ∧ col i = col j then 1 else 0) = npairs col := by sorry

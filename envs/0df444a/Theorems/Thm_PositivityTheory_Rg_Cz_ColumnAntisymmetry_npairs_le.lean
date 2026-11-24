-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_npairs_le
-- name    : PositivityTheory.Rg.Cz.ColumnAntisymmetry.npairs_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:06.36326+00:00
-- url     : https://prove2.me/theorems/44d78c48-6d48-4d42-bf00-8bec59b0a4a5
-- title:
--   Column Antisymmetry: npairs le
-- statement:
--   The Column Antisymmetry construction uses the npairs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiB.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiB.lean#L74-L77

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiB
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

theorem PositivityTheory.Rg.Cz.ColumnAntisymmetry.npairs_le {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (I : Fin m → Fin n)
    (hI : ColInj col I) : npairs col ≤ ∑ p, ((top : ℕ) - I p) := by sorry

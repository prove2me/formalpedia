-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_rk_le
-- name    : PositivityTheory.Rg.Cz.ColumnAntisymmetry.rk_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:12.872079+00:00
-- url     : https://prove2.me/theorems/65085ec1-d6ce-4de4-8cef-41703af51b4e
-- title:
--   Column Antisymmetry: rk le
-- statement:
--   The Column Antisymmetry construction uses the rk le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiB.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiB.lean#L22-L34

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

theorem PositivityTheory.Rg.Cz.ColumnAntisymmetry.rk_le {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (I : Fin m → Fin n)
    (hI : ColInj col I) (p : Fin m) : rk col I p ≤ (top : ℕ) - I p := by sorry

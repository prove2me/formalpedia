-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_pm_single
-- name    : PositivityTheory.Rg.Cz.ColumnAntisymmetry.pm_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:53.177298+00:00
-- url     : https://prove2.me/theorems/1b95f135-a5c8-52bb-92f9-7493cb7bd81b
-- title:
--   Column Antisymmetry: pm single
-- statement:
--   The Column Antisymmetry construction uses the pm single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAnti.lean#L120-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAnti.lean#L120-L128

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAnti
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
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ}

theorem PositivityTheory.Rg.Cz.ColumnAntisymmetry.pm_single (σ : Equiv.Perm (Fin m)) (I : Fin m → Fin n) (v : M) :
    pm σ (Pi.single I v : TV n M (Fin m)) = Pi.single (I ∘ ⇑σ⁻¹) v := by sorry

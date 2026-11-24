-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_Q_mul
-- name    : PositivityTheory.Rg.Cz.ColumnAntisymmetry.Q_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:58.431686+00:00
-- url     : https://prove2.me/theorems/79f8c899-2a4b-4d56-a501-2b574cc4e7d5
-- title:
--   Column Antisymmetry: Q mul
-- statement:
--   The Column Antisymmetry construction uses the Q mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAnti.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAnti.lean#L17-L23

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

theorem PositivityTheory.Rg.Cz.ColumnAntisymmetry.Q_mul (L : TV n M (Fin m) →ₗ[ℂ] ℂ) {σ τ : Equiv.Perm (Fin m)} (h1 : Q L σ) (h2 : Q L τ) :
    Q L (σ * τ) := by sorry

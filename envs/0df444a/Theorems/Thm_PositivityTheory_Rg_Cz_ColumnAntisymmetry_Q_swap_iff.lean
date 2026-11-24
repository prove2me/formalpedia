-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_Q_swap_iff
-- name    : PositivityTheory.Rg.Cz.ColumnAntisymmetry.Q_swap_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:09.964796+00:00
-- url     : https://prove2.me/theorems/8400e956-fc1e-4754-812f-5d50e31eeb2a
-- title:
--   Column Antisymmetry: Q swap iff
-- statement:
--   The Column Antisymmetry construction uses the Q swap iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAnti.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAnti.lean#L29-L33

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

theorem PositivityTheory.Rg.Cz.ColumnAntisymmetry.Q_swap_iff (L : TV n M (Fin m) →ₗ[ℂ] ℂ) {p q : Fin m} (h : p ≠ q) :
    Q L (Equiv.swap p q) ↔ L ∘ₗ pm (Equiv.swap p q) = -L := by sorry

-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_split
-- name    : PositivityTheory.Rg.Cz.ColumnAntisymmetry.split
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:53:37.839141+00:00
-- url     : https://prove2.me/theorems/78330ed1-10af-5f98-8707-a148309b740c
-- title:
--   Column Antisymmetry: split
-- statement:
--   The Column Antisymmetry construction uses the split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiC.lean#L13-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiC.lean#L13-L198

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiC
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

theorem PositivityTheory.Rg.Cz.ColumnAntisymmetry.split {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (col : Fin m → ℕ) (hmono : Monotone col)
    (hc : ∀ i j : Fin m, Commute (xJ E i) (xJ E j))
    (hP : ∀ i j : Fin m, (i : ℕ) + 1 = j →
      xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 ∧
      ∀ k : Fin m, k ≠ i → k ≠ j → Commute (xJ E k) (pm (Equiv.swap i j)))
    (i j : Fin m) (hij : (i : ℕ) + 1 = j) (hcol : col i = col j) :
    ∃ R : Module.End ℂ (TV n M (Fin m)), colD E col = (xJ E i - xJ E j + 1) * R ∧
      R * pm (Equiv.swap i j) = pm (Equiv.swap i j) * R := by sorry

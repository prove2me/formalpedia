-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_eq_of_le
-- name    : PositivityTheory.Rg.Cz.ColumnAntisymmetry.eq_of_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:48:54.046831+00:00
-- url     : https://prove2.me/theorems/a712fed0-4c14-44f7-a7ee-aa85aa028781
-- title:
--   Column Antisymmetry: eq of le
-- statement:
--   The Column Antisymmetry construction uses the eq of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiB.lean#L79-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiB.lean#L79-L129

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

theorem PositivityTheory.Rg.Cz.ColumnAntisymmetry.eq_of_le {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (b I : Fin m → Fin n)
    (hb : IsTab col b) (hI : ColInj col I) (h : ∑ p, ((top : ℕ) - I p) ≤ npairs col) :
    ∃ σ ∈ colG col, I = b ∘ σ := by sorry

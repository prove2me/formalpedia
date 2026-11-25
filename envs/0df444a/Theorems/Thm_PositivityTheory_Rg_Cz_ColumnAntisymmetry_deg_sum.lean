-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_deg_sum
-- name    : PositivityTheory.Rg.Cz.ColumnAntisymmetry.deg_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:48:36.929824+00:00
-- url     : https://prove2.me/theorems/eff45667-d130-48c7-9eb7-dfad89c8955f
-- title:
--   Column Antisymmetry: deg sum
-- statement:
--   The Column Antisymmetry construction uses the deg sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiA.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiA.lean#L40-L43

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

theorem PositivityTheory.Rg.Cz.ColumnAntisymmetry.deg_sum {d : ℕ} (s : Finset (Fin m)) (f : Fin m → Module.End ℂ (TV n M (Fin m)))
    (hf : ∀ i ∈ s, Deg E d (f i)) : Deg E d (∑ i ∈ s, f i) := by sorry

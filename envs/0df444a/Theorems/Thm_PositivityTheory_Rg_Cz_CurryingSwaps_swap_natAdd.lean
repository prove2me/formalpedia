-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CurryingSwaps_swap_natAdd
-- name    : PositivityTheory.Rg.Cz.CurryingSwaps.swap_natAdd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:24.255989+00:00
-- url     : https://prove2.me/theorems/fef83ee0-91b9-46af-88b1-90875df963d8
-- title:
--   Currying Swaps: swap nat Add
-- statement:
--   The Currying Swaps construction uses the swap nat Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PCurry.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PCurry.lean#L43-L51

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PCurry
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
open PositivityTheory.Rg.Cz.CurryingSwaps
variable {α : Type*} {m k : ℕ}

theorem PositivityTheory.Rg.Cz.CurryingSwaps.swap_natAdd (I : Fin m → α) (J : Fin k → α) (j j' : Fin k) :
    Fin.append I J ∘ Equiv.swap (Fin.natAdd m j) (Fin.natAdd m j') = Fin.append I (J ∘ Equiv.swap j j') := by sorry

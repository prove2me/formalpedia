-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CurryingSwaps_upd_natAdd
-- name    : PositivityTheory.Rg.Cz.CurryingSwaps.upd_natAdd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:54.38513+00:00
-- url     : https://prove2.me/theorems/fe1d4fd7-89e9-4402-8fd8-29f90a2e1df6
-- title:
--   Currying Swaps: upd nat Add
-- statement:
--   The Currying Swaps construction uses the upd nat Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PCurry.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PCurry.lean#L23-L31

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

theorem PositivityTheory.Rg.Cz.CurryingSwaps.upd_natAdd (I : Fin m → α) (J : Fin k → α) (j : Fin k) (v : α) :
    Function.update (Fin.append I J) (Fin.natAdd m j) v = Fin.append I (Function.update J j v) := by sorry

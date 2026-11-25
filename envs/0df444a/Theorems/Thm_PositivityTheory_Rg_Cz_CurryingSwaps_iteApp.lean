-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CurryingSwaps_iteApp
-- name    : PositivityTheory.Rg.Cz.CurryingSwaps.iteApp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:46.143667+00:00
-- url     : https://prove2.me/theorems/577e258e-5b48-5c32-8814-78d6015a4be5
-- title:
--   Currying Swaps: ite App
-- statement:
--   The Currying Swaps construction uses the ite App property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PCurry.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PCurry.lean#L71-L73

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

theorem PositivityTheory.Rg.Cz.CurryingSwaps.iteApp {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (p : Prop) [Decidable p]
    (g : V →ₗ[ℂ] W) (x : V) : (if p then g else 0) x = if p then g x else 0 := by sorry

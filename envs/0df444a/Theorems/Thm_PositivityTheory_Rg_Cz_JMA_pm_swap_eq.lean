-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_JMA_pm_swap_eq
-- name    : PositivityTheory.Rg.Cz.JMA.pm_swap_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:49:11.149794+00:00
-- url     : https://prove2.me/theorems/684c210b-efb5-46f0-a1a3-539f1c5301fe
-- title:
--   JMA: pm swap eq
-- statement:
--   The JMA construction uses the pm swap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PJmComm.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PJmComm.lean#L19-L25

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
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
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.JMA.pm_swap_eq {P : Type} [DecidableEq P] (p j : P) (h : p ≠ j) :
    (pm (Equiv.swap p j) : Module.End ℂ (TV n M P)) = ∑ a, ∑ b, eAt p a b * eAt j b a := by sorry

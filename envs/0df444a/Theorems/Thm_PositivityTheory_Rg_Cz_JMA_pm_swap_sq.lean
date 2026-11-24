-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_JMA_pm_swap_sq
-- name    : PositivityTheory.Rg.Cz.JMA.pm_swap_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:23.398269+00:00
-- url     : https://prove2.me/theorems/7778bc88-0abe-4ea7-87b6-af4021ec57c7
-- title:
--   JMA: pm swap sq
-- statement:
--   The JMA construction uses the pm swap sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PJmComm.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PJmComm.lean#L90-L92

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

theorem PositivityTheory.Rg.Cz.JMA.pm_swap_sq {P : Type} (i j : P) [DecidableEq P] :
    (pm (Equiv.swap i j) : Module.End ℂ (TV n M P)) * pm (Equiv.swap i j) = 1 := by sorry

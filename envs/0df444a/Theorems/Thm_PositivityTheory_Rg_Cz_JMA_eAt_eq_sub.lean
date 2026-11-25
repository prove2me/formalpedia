-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_JMA_eAt_eq_sub
-- name    : PositivityTheory.Rg.Cz.JMA.eAt_eq_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:10.378225+00:00
-- url     : https://prove2.me/theorems/302a80ef-1b85-478f-a781-a90b99040d6f
-- title:
--   JMA: e At eq sub
-- statement:
--   The JMA construction uses the e At eq sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PJmComm.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PJmComm.lean#L40-L44

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

theorem PositivityTheory.Rg.Cz.JMA.eAt_eq_sub {P : Type} [DecidableEq P] (S : Finset P) (j : P) (hj : j ∉ S)
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    (eAt j a b : Module.End ℂ (TV n M P)) = tE (insert j S) E a b - tE S E a b := by sorry

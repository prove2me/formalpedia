-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_omc_update
-- name    : PositivityTheory.Rg.Cz.CtrX.omc_update
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:54.454436+00:00
-- url     : https://prove2.me/theorems/2a103322-325c-4251-85b8-1c93fb8af5a3
-- title:
--   Ctr X: omc update
-- statement:
--   The Ctr X construction uses the omc update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractE.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractE.lean#L40-L47

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
omit [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.CtrX.omc_update {m : ℕ} (j : Fin m) (a b : Fin n) (R : {p // p ≠ j} → Fin n) :
    Function.update (omcGlue j b R) j a = omcGlue j a R := by sorry

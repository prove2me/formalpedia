-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_omc_prod
-- name    : PositivityTheory.Rg.Cz.CtrX.omc_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:09.815492+00:00
-- url     : https://prove2.me/theorems/0118d05a-9a84-4bb0-bd92-58622f09c5c9
-- title:
--   Ctr X: omc prod
-- statement:
--   The Ctr X construction uses the omc prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractE.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractE.lean#L50-L56

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

theorem PositivityTheory.Rg.Cz.CtrX.omc_prod {m : ℕ} (j : Fin m) (F : Fin m → Fin n → ℂ) (b : Fin n) (R : {p // p ≠ j} → Fin n) :
    ∏ p, F p (omcGlue j b R p) = F j b * ∏ p : {p // p ≠ j}, F p.1 (R p) := by sorry

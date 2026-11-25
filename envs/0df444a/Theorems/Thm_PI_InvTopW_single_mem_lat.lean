-- Prove2me | Theorems.Thm_PI_InvTopW_single_mem_lat
-- name    : PI.InvTopW.single_mem_lat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:17.517848+00:00
-- url     : https://prove2.me/theorems/e932678e-f21b-54cc-b7a7-163c32f6abc9
-- title:
--   Inv Top W: single mem lat
-- statement:
--   The Inv Top W construction uses the single mem lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L178-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L178-L190

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.InvTopW.single_mem_lat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (c : ℕ)
    (hs : ∀ j, (c : E) • Pi.single j (1 : E) ∈ L) (j : Fin n) :
    Pi.single j (c : E ⊗[F] Formalism.MainNotions.S.Af F) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by sorry

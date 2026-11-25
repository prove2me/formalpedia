-- Prove2me | Theorems.Thm_PI_InvTopW_lat_den
-- name    : PI.InvTopW.lat_den
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:01.407765+00:00
-- url     : https://prove2.me/theorems/6addb0af-a0d6-442f-9244-83753834bf2f
-- title:
--   Inv Top W: lat den
-- statement:
--   The Inv Top W construction uses the lat den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L147-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L147-L176

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

theorem PI.InvTopW.lat_den {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (c : ℕ)
    (hc : ∀ x ∈ L, ∀ i, (c : E) * x i ∈ Formalism.UG.intOE E) :
    ∀ y ∈ Formalism.MainNotions.S.lamAf (F := F) L, ∀ i,
      (c : E ⊗[F] Formalism.MainNotions.S.Af F) * y i ∈ Formalism.MainNotions.S.IntAf F E := by sorry

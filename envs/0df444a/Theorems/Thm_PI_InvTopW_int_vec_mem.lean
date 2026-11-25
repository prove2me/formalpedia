-- Prove2me | Theorems.Thm_PI_InvTopW_int_vec_mem
-- name    : PI.InvTopW.int_vec_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:49.364497+00:00
-- url     : https://prove2.me/theorems/60020ee5-1614-4ae9-9dfd-4dba3d3bb596
-- title:
--   Inv Top W: int vec mem
-- statement:
--   The Inv Top W construction uses the int vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L192-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L192-L202

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

theorem PI.InvTopW.int_vec_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (c : ℕ)
    (hs : ∀ j, (c : E) • Pi.single j (1 : E) ∈ L) (u : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F)
    (hu : ∀ i, u i ∈ Formalism.MainNotions.S.IntAf F E) :
    (fun i => (c : E ⊗[F] Formalism.MainNotions.S.Af F) * u i) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by sorry

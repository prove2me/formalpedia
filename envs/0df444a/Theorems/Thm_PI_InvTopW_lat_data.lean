-- Prove2me | Theorems.Thm_PI_InvTopW_lat_data
-- name    : PI.InvTopW.lat_data
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:10.861567+00:00
-- url     : https://prove2.me/theorems/e384750c-7388-5317-b496-25c73595f9af
-- title:
--   Inv Top W: lat data
-- statement:
--   The Inv Top W construction uses the lat data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L206-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L206-L211

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

theorem PI.InvTopW.lat_data (I : AutInst) : ∃ c : ℕ, 1 ≤ c ∧
    (∀ y ∈ I.Lf, ∀ i, (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * y i ∈ Formalism.MainNotions.S.IntAf I.F I.E) ∧
    ∀ u : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, (∀ i, u i ∈ Formalism.MainNotions.S.IntAf I.F I.E) →
      (fun i => (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * u i) ∈ I.Lf := by sorry

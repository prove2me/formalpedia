-- Prove2me | Theorems.Thm_PI_InvTopW_exists_good_den
-- name    : PI.InvTopW.exists_good_den
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:41.440972+00:00
-- url     : https://prove2.me/theorems/f2f5d9ef-ea39-4c32-b098-abe25c3fb43d
-- title:
--   Inv Top W: exists good den
-- statement:
--   The Inv Top W construction uses the exists good den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L120-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L120-L134

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

theorem PI.InvTopW.exists_good_den {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hF : L.FG)
    (hS : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ c : ℕ, 1 ≤ c ∧ (∀ x ∈ L, ∀ i, (c : E) * x i ∈ Formalism.UG.intOE E) ∧
      ∀ j, (c : E) • Pi.single j (1 : E) ∈ L := by sorry

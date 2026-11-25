-- Prove2me | Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_atN_map
-- name    : PI.UnfoldEquiv.UnitaryGroupMassFormula.atN_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:04.856719+00:00
-- url     : https://prove2.me/theorems/fe46e869-6eb9-58ef-9b8a-e5e8af48ce14
-- title:
--   Unitary Group Mass Formula: at N map
-- statement:
--   The Unitary Group Mass Formula construction uses the at N map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/CompSymmComp.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/CompSymmComp.lean#L11-L31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_Points
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_CompSymmComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
open PI PI.UnfoldEquiv PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]

theorem PI.UnfoldEquiv.UnitaryGroupMassFormula.atN_map {n c i : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hi : i < c)
    {w : Fin (n + c) → k} (hw : w ∈ Ufl k n c (i + 1)) : atN (r w) (n + i) = atN w (n + i) := by sorry

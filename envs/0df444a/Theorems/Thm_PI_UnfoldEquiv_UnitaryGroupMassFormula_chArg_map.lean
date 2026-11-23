-- Prove2me | Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_chArg_map
-- name    : PI.UnfoldEquiv.UnitaryGroupMassFormula.chArg_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:04.154352+00:00
-- url     : https://prove2.me/theorems/477226a0-57d7-4a0f-84a8-1d66fe7e2c58
-- title:
--   Unitary Group Mass Formula: ch Arg map
-- statement:
--   The Unitary Group Mass Formula construction uses the ch Arg map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/CompSymmComp.lean#L42-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/CompSymmComp.lean#L42-L74

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

theorem PI.UnfoldEquiv.UnitaryGroupMassFormula.chArg_map {n' n c : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r)
    {xj : (Fin n' → k) →ₗ[k] (Fin n → k)} {x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)} (h : Q xj x) :
    chArg (n' := n') (c' := c + 1) (n := n) (c := c) (r.toLinearMap ∘ₗ x) = chArg x + n1Arg r := by sorry

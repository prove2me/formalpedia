-- Prove2me | Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_Q_map
-- name    : PI.UnfoldEquiv.UnitaryGroupMassFormula.Q_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:06.565938+00:00
-- url     : https://prove2.me/theorems/c3bdf3bb-c1f3-499a-8576-f7e29d2becb6
-- title:
--   Unitary Group Mass Formula: Q map
-- statement:
--   The Unitary Group Mass Formula construction uses the Q map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/Points.lean#L122-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/Points.lean#L122-L139

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_Points
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

theorem PI.UnfoldEquiv.UnitaryGroupMassFormula.Q_map {n' n c : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} {g : (Fin n → k) ≃ₗ[k] (Fin n → k)}
    (hr : R1cond k n c r) (hg : ∀ x, r (inX k n c x) = inX k n c (g x)) {xj : (Fin n' → k) →ₗ[k] (Fin n → k)}
    {x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)} (h : Q xj x) :
    Q (g.toLinearMap ∘ₗ xj) (r.toLinearMap ∘ₗ x) := by sorry

-- Prove2me | Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_Q_iff
-- name    : PI.UnfoldEquiv.UnitaryGroupMassFormula.Q_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:45.157308+00:00
-- url     : https://prove2.me/theorems/1faa173b-3493-4fc9-b546-f577ff7caf0e
-- title:
--   Unitary Group Mass Formula: Q iff
-- statement:
--   The Unitary Group Mass Formula construction uses the Q iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/Points.lean#L37-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/Points.lean#L37-L106

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

theorem PI.UnfoldEquiv.UnitaryGroupMassFormula.Q_iff {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) :
    Q xj x ↔ ∀ (l : Fin (n + c)) (s : Fin (n' + (c + 1))), ¬ IsFree n' n c l.1 s.1 → x (Pi.single s 1) l = base xj l s := by sorry

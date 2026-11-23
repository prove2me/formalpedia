-- Prove2me | Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_mem_Ufl
-- name    : PI.UnfoldEquiv.UnitaryGroupMassFormula.mem_Ufl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:50.22439+00:00
-- url     : https://prove2.me/theorems/6cf70967-0143-4bc7-908a-9b9e95c18800
-- title:
--   Unitary Group Mass Formula: mem Ufl
-- statement:
--   The Unitary Group Mass Formula construction uses the mem Ufl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/ExtractFreeFillMatrix.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/ExtractFreeFillMatrix.lean#L13-L14

import Definitions.Def_Formalism_PeriodIntegrals_UnfoldEquiv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix
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

theorem PI.UnfoldEquiv.UnitaryGroupMassFormula.mem_Ufl {n c i : ℕ} {v : Fin (n + c) → k} :
    v ∈ Ufl k n c i ↔ ∀ l : Fin (n + c), ¬ (l.1 < n + i) → v l = 0 := by sorry

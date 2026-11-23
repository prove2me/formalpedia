-- Prove2me | Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_fillMatrix_single
-- name    : PI.UnfoldEquiv.UnitaryGroupMassFormula.fillMatrix_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:40.206773+00:00
-- url     : https://prove2.me/theorems/99d22dff-aea8-45b5-af7d-7b6115f5d2a0
-- title:
--   Unitary Group Mass Formula: fill Matrix single
-- statement:
--   The Unitary Group Mass Formula construction uses the fill Matrix single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/ExtractFreeFillMatrix.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/ExtractFreeFillMatrix.lean#L59-L63

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

theorem PI.UnfoldEquiv.UnitaryGroupMassFormula.fillMatrix_single {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' (c + 1) n c → k)
    (l : Fin (n + c)) (s : Fin (n' + (c + 1))) :
    xx1 xj t (Pi.single s 1) l = if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩ else base xj l s := by sorry

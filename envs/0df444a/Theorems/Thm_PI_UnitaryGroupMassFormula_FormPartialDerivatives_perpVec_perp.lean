-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FormPartialDerivatives_perpVec_perp
-- name    : PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_perp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:37.194183+00:00
-- url     : https://prove2.me/theorems/0ed29961-0197-5129-86b5-4bb74207dd8a
-- title:
--   Form Partial Derivatives: perp Vec perp
-- statement:
--   The Form Partial Derivatives construction uses the perp Vec perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/PerpendicularDeterminants/PerpVecOfPerp.lean#L8-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/PerpendicularDeterminants/PerpVecOfPerp.lean#L8-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_PerpVecPerpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_PerpVecOfPerp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FormPartialDerivatives
open ReciprocityTheory.ChartRestriction.G.TB

theorem PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_perp (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (c : Fin p) :
    h (perpVec h e e' g) (e c) = 0 := by sorry

-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FormPartialDerivatives_perpVec_of_perp
-- name    : PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_of_perp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:56.189816+00:00
-- url     : https://prove2.me/theorems/de933dde-dbad-4bff-9202-16f03a113f05
-- title:
--   Form Partial Derivatives: perp Vec of perp
-- statement:
--   The Form Partial Derivatives construction uses the perp Vec of perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/PerpendicularDeterminants/PerpVecOfPerp.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/PerpendicularDeterminants/PerpVecOfPerp.lean#L58-L61

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

theorem PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_of_perp (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (hg : ∀ a, h g (e a) = 0) :
    perpVec h e e' g = (hMat h e e').det • g := by sorry

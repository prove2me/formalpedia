-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FormPartialDerivatives_perpVec_int
-- name    : PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_int
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:46.604139+00:00
-- url     : https://prove2.me/theorems/df004fcb-45f2-4c12-8916-771a95ba1c50
-- title:
--   Form Partial Derivatives: perp Vec int
-- statement:
--   The Form Partial Derivatives construction uses the perp Vec int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/PerpendicularDeterminants/PerpVecOfPerp.lean#L36-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/PerpendicularDeterminants/PerpVecOfPerp.lean#L36-L56

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

theorem PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_int (R : Type) [CommRing R] (O : Subring R) (V : Type) [AddCommGroup V] [Module R V]
    (p : ℕ) (h : V →ₗ[R] (V → R)) (L : Submodule O V)
    (hL : ∀ u ∈ L, ∀ v ∈ L, h u v ∈ O) (e e' : Fin p → V) (g : V)
    (he : ∀ a, e a ∈ L) (he' : ∀ a, e' a ∈ L) (hg : g ∈ L) : perpVec h e e' g ∈ L := by sorry

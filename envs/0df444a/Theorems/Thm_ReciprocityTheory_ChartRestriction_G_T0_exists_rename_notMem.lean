-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_exists_rename_notMem
-- name    : ReciprocityTheory.ChartRestriction.G.T0.exists_rename_notMem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:34.194904+00:00
-- url     : https://prove2.me/theorems/08ab3cf8-aa71-4630-ae1a-4fafcf2a3b9c
-- title:
--   T0: exists rename not Mem
-- statement:
--   The T0 construction uses the exists rename not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValAlgebraMapEqZero.lean#L8-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValAlgebraMapEqZero.lean#L8-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValAlgebraMapEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial

theorem ReciprocityTheory.ChartRestriction.G.T0.exists_rename_notMem {K : Type} [Field K] {σ : Type} (p : Ideal (MvPolynomial σ K))
    (hp : p.IsPrime ∧ p.height = 1) :
    ∃ e0 : σ, ∀ q : MvPolynomial {e // e ≠ e0} K, q ≠ 0 → rename Subtype.val q ∉ p := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_card_baseOrOffColumn
-- name    : ReciprocityTheory.ChartRestriction.G.T0.card_baseOrOffColumn
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:37:29.644679+00:00
-- url     : https://prove2.me/theorems/d68ec8a6-ea6d-56a8-b796-fa1672ef4f27
-- title:
--   T0: card base Or Off Column
-- statement:
--   The T0 construction uses the card base Or Off Column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValAlgebraMapEqZero.lean#L86-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValAlgebraMapEqZero.lean#L86-L106

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

theorem ReciprocityTheory.ChartRestriction.G.T0.card_baseOrOffColumn {D N : ℕ} (j0 : Fin (N + 1)) :
    Fintype.card {e : TVar D N // e.1 = 0 ∨ e.2 ≠ j0} = (D + 1) * (N + 1) - D := by sorry

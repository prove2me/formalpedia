-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_inv_entry__eb51cf5bfe54
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_inv_entry__eb51cf5bfe54
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:55.43307+00:00
-- url     : https://prove2.me/theorems/dfbde521-fc02-4d76-89e9-d99048b9e5b7
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up sum Bd inv entry  eb51cf5bfe54: P2 M Reciprocity Theory Chart Restriction G AR Up sum Bd inv entry  eb51cf5bfe54
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up sum Bd inv entry  eb51cf5bfe54 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up sum Bd inv entry  eb51cf5bfe54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfB.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfB.lean#L102-L106

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_inv_entry__eb51cf5bfe54 {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g)
    (i j : Fin p ⊕ Fin q) : ‖g⁻¹ i j‖ = ‖g j i‖ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«sumBd_inv_entry'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_inv_entry__eb51cf5bfe54

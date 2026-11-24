-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_C_mul_of_map_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.L1.exists_C_mul_of_map_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:37:08.164384+00:00
-- url     : https://prove2.me/theorems/c5546902-59a9-425d-a720-e6f8f6be083d
-- title:
--   L1: exists C mul of map eq zero
-- statement:
--   The L1 construction uses the exists C mul of map eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFrobSer.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFrobSer.lean#L23-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.exists_C_mul_of_map_eq_zero {p : ℕ} (h : PowerSeries ℤ)
    (h0 : h.map (Int.castRingHom (ZMod p)) = 0) :
    ∃ g : PowerSeries ℤ, h = PowerSeries.C (p : ℤ) * g := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_of_int
-- name    : ReciprocityTheory.ChartRestriction.L1.Cg.of_int
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:58:11.665995+00:00
-- url     : https://prove2.me/theorems/3febc141-3a4c-428c-924e-b9abbd9c7997
-- title:
--   Cg: of int
-- statement:
--   The Cg construction uses the of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModKronSer.lean#L85-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModKronSer.lean#L85-L94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
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

theorem ReciprocityTheory.ChartRestriction.L1.Cg.of_int {p : ℕ} (hp : p.Prime) {F G W : PowerSeries ℤ} (h : F = G + PowerSeries.C (p : ℤ) * W) :
    Cg p (F.map (Int.castRingHom ℂ)) (G.map (Int.castRingHom ℂ)) := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_facSer_Cg_b
-- name    : ReciprocityTheory.ChartRestriction.L1.facSer_Cg_b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:00.328414+00:00
-- url     : https://prove2.me/theorems/3757e297-81b9-5791-ae4e-c2fb3971d5c4
-- title:
--   L1: fac Ser Cg b
-- statement:
--   The L1 construction uses the fac Ser Cg b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModKronSer.lean#L183-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModKronSer.lean#L183-L194

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_xp

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

theorem ReciprocityTheory.ChartRestriction.L1.facSer_Cg_b {p : ℕ} (hp : p.Prime) (b : ℕ) :
    Cg p (facSer p (1, b, p)) (xp p aC * dC - aC * xp p dC) := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_facSer_ev
-- name    : ReciprocityTheory.ChartRestriction.L1.facSer_ev
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:43:29.899208+00:00
-- url     : https://prove2.me/theorems/92079764-54e1-4f9b-a61d-aeb7b5d1303e
-- title:
--   L1: fac Ser ev
-- statement:
--   The L1 construction uses the fac Ser ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFacSer.lean#L108-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFacSer.lean#L108-L125

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFacSer
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

theorem ReciprocityTheory.ChartRestriction.L1.facSer_ev {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (τ : ℍ) :
    ev (facSer m t) (qm m τ) = fac t τ := by sorry

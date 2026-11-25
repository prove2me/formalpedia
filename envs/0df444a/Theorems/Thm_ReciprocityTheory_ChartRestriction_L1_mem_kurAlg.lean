-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_mem_kurAlg
-- name    : ReciprocityTheory.ChartRestriction.L1.mem_kurAlg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:17.835278+00:00
-- url     : https://prove2.me/theorems/539d5241-801c-5777-b669-95c654c6c0e3
-- title:
--   L1: mem kur Alg
-- statement:
--   The L1 construction uses the mem kur Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLocB.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLocB.lean#L47-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorHensel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.mem_kurAlg {l : ℕ} [Fact l.Prime] {y : PadicAlgCl l} :
    y ∈ kurAlg l ↔ algebraMap (PadicAlgCl l) ℂ_[l] y ∈ MaximalUnramifiedExtension l := by sorry

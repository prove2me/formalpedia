-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_mem_multiLt_iff
-- name    : ReciprocityTheory.ChartRestriction.G.AR.mem_multiLt_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:18.97193+00:00
-- url     : https://prove2.me/theorems/e6a80640-acf5-44d9-ae48-1a7e025ebdc4
-- title:
--   AR: mem multi Lt iff
-- statement:
--   The AR construction uses the mem multi Lt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/JetsPf.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/JetsPf.lean#L5-L6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetIndepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetsPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR

theorem ReciprocityTheory.ChartRestriction.G.AR.mem_multiLt_iff {D a : ℕ} {α : Fin D → ℕ} : α ∈ multiLt D a ↔ ∑ k, α k < a := by sorry

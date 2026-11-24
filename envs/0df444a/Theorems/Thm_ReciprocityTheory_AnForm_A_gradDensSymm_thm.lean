-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_gradDensSymm_thm
-- name    : ReciprocityTheory.AnForm.A.gradDensSymm_thm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:11.646401+00:00
-- url     : https://prove2.me/theorems/fec731c7-3511-4863-8fdf-0e677411758c
-- title:
--   A: grad Dens Symm thm
-- statement:
--   The A construction uses the grad Dens Symm thm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L232-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L232-L238

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.A.gradDensSymm_thm : GradDensSymmStatement := by sorry

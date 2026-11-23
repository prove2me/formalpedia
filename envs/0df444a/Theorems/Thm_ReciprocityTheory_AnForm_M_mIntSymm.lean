-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_mIntSymm
-- name    : ReciprocityTheory.AnForm.M.mIntSymm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:16.020809+00:00
-- url     : https://prove2.me/theorems/026137af-b81c-400b-82d8-eff50fd36484
-- title:
--   M: m Int Symm
-- statement:
--   The M construction uses the m Int Symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PotentialContDiffAt.lean#L99-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PotentialContDiffAt.lean#L99-L108

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff ComplexOrder
noncomputable section

theorem ReciprocityTheory.AnForm.M.mIntSymm : MIntSymmStatement := by sorry

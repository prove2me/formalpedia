-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_normOrd
-- name    : ReciprocityTheory.L2DbarEstimates.normOrd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:40.564557+00:00
-- url     : https://prove2.me/theorems/61edbe30-01c6-4cee-a25c-52ac70552149
-- title:
--   L2 Dbar Estimates: norm Ord
-- statement:
--   The L2 Dbar Estimates construction uses the norm Ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/NormFibrations/NormOrd.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/NormFibrations/NormOrd.lean#L17-L32

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_HoloSectionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_NormOrd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology

theorem ReciprocityTheory.L2DbarEstimates.normOrd : NormOrdStatement.{u} := by sorry

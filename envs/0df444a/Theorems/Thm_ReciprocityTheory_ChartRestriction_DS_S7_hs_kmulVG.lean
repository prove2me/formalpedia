-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_kmulVG
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.hs_kmulVG
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:55.058055+00:00
-- url     : https://prove2.me/theorems/bb7abc43-7e42-4702-8ffc-243ee5ed0ddd
-- title:
--   S7: hs kmul VG
-- statement:
--   The S7 construction uses the hs kmul VG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IntegrableOfDecayVG.lean#L298-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IntegrableOfDecayVG.lean#L298-L301

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.hs_kmulVG {ε : Fin n → Bool} (k : KG ε) (A : Matrix (Fin n) (Fin n) ℂ) : hs (toMK k * A) = hs A := by sorry

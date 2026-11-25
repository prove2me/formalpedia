-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_sg__Multi_6b63c33631c3
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_sg__Multi_6b63c33631c3
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:12:33.497642+00:00
-- url     : https://prove2.me/theorems/fcc531ac-f33d-5f82-b8d9-24d23ebbb2f5
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS sg  Multi 6b63c33631c3: P2 M Reciprocity Theory Chart Restriction DS sg  Multi 6b63c33631c3
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS sg  Multi 6b63c33631c3 construction uses the P2 M Reciprocity Theory Chart Restriction DS sg  Multi 6b63c33631c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L102-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L102-L110

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_sg__Multi_6b63c33631c3 (ε : Fin n → Bool) (c : Fin n) {k : ℕ} (v : Fin k → Fin n × Fin n) :
    sgE ε cpFock cmFock c c (ExteriorAlgebra.ιMulti ℂ k (fun i => Pi.single (v i) (1 : ℂ))) =
      ((∑ i, modeWt ε (v i) c : ℝ) : ℂ) • ExteriorAlgebra.ιMulti ℂ k (fun i => Pi.single (v i) (1 : ℂ)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«sg_ιMulti» := P2M_ReciprocityTheory_ChartRestriction_DS_sg__Multi_6b63c33631c3

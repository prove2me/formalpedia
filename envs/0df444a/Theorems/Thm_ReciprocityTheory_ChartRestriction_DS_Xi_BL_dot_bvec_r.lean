-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_dot_bvec_r
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.dot_bvec_r
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:26:30.297341+00:00
-- url     : https://prove2.me/theorems/9e2f52b0-16db-42e1-a082-621beadb3461
-- title:
--   BL: dot bvec r
-- statement:
--   The BL construction uses the dot bvec r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermExpand.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermExpand.lean#L23-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.dot_bvec_r {n : ℕ} (i : Fin n) (x : Fin n → ℂ) : x ⬝ᵥ bvec i = x i := by sorry

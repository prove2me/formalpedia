-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_eq_mul_exp_neg_polar_L_mul_exp_polar_L
-- name    : ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.eq_mul_exp_neg_polar_L_mul_exp_polar_L
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:25.782283+00:00
-- url     : https://prove2.me/theorems/71c024ce-f3f9-44e8-bcf9-e532e3d484a9
-- title:
--   Polar Decomposition: eq mul exp neg polar L mul exp polar L
-- statement:
--   The Polar Decomposition construction uses the eq mul exp neg polar L mul exp polar L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/PolarJmConjTranspose.lean#L207-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/PolarJmConjTranspose.lean#L207-L209

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.PolarDecomposition

theorem ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.eq_mul_exp_neg_polar_L_mul_exp_polar_L {g : Matrix (Fin n) (Fin n) ℂ} :
    g = g * NormedSpace.exp (-polar_L g) * NormedSpace.exp (polar_L g) := by sorry

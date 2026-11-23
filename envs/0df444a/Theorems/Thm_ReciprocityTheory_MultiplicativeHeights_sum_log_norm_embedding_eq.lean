-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sum_log_norm_embedding_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:03.502794+00:00
-- url     : https://prove2.me/theorems/789b810d-1b3a-4ef9-8200-fe60b2e017cc
-- title:
--   Multiplicative Heights: sum log norm embedding eq
-- statement:
--   The Multiplicative Heights construction uses the sum log norm embedding eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LogNormCoeffSubLeBlockSphereLogMean.lean#L119-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LogNormCoeffSubLeBlockSphereLogMean.lean#L119-L129

import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_LogNormCoeffSubLeBlockSphereLogMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial NumberField

theorem ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq {K : Type*} [Field K] [NumberField K] (c : K) (hc : c ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = Real.log |((Algebra.norm ℚ c : ℚ) : ℝ)| := by sorry

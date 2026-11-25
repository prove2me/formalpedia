-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_neg_log_norm_coeff_le_finitePlaces
-- name    : ReciprocityTheory.MultiplicativeHeights.neg_log_norm_coeff_le_finitePlaces
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:35.556832+00:00
-- url     : https://prove2.me/theorems/26cd5f4b-6f2d-4a8b-b0d2-bde9d1577ec9
-- title:
--   Multiplicative Heights: neg log norm coeff le finite Places
-- statement:
--   The Multiplicative Heights construction uses the neg log norm coeff le finite Places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LogNormCoeffSubLeBlockSphereLogMean.lean#L73-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LogNormCoeffSubLeBlockSphereLogMean.lean#L73-L117

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

theorem ReciprocityTheory.MultiplicativeHeights.neg_log_norm_coeff_le_finitePlaces {K : Type*} [Field K] [NumberField K] {ι : Type*} (f : MvPolynomial ι K)
    (s : ι →₀ ℕ) (hs : s ∈ f.support) :
    -Real.log |((Algebra.norm ℚ (f.coeff s) : ℚ) : ℝ)| ≤
      ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f) := by sorry

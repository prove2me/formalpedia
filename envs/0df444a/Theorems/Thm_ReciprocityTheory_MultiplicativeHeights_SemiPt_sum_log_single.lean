-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_sum_log_single
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.sum_log_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:01.010829+00:00
-- url     : https://prove2.me/theorems/14007d81-b412-4ec8-9bd1-09a87f307795
-- title:
--   Semi Pt: sum log single
-- statement:
--   The Semi Pt construction uses the sum log single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegR.lean#L42-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegR.lean#L42-L53

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.sum_log_single {K : Type} [Field K] [NumberField K] (z : K) (hz : z ≠ 0) (d : ℝ)
    (hd : 0 < d) :
    ∑ σ : K →+* ℂ, Real.log (‖σ z‖ ^ 2 * d) =
      2 * Real.log |((Algebra.norm ℚ z : ℚ) : ℝ)| + (Fintype.card (K →+* ℂ) : ℝ) * Real.log d := by sorry

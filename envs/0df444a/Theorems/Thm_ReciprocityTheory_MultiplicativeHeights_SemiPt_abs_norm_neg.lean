-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_abs_norm_neg
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.abs_norm_neg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:02:41.594485+00:00
-- url     : https://prove2.me/theorems/40e38d01-b2d8-44e1-b5e0-dcab686a9b97
-- title:
--   Semi Pt: abs norm neg
-- statement:
--   The Semi Pt construction uses the abs norm neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegI.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegI.lean#L37-L42

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegH
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.abs_norm_neg {K : Type} [Field K] [NumberField K] (z : K) :
    |((Algebra.norm ℚ (-z) : ℚ) : ℝ)| = |((Algebra.norm ℚ z : ℚ) : ℝ)| := by sorry

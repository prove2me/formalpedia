-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_isIntegralElt_add
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.isIntegralElt_add
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:13.042198+00:00
-- url     : https://prove2.me/theorems/ad620eb8-1b09-4e5e-8811-21285145d9bf
-- title:
--   Semi Pt: is Integral Elt add
-- statement:
--   The Semi Pt construction uses the is Integral Elt add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegH.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegH.lean#L10-L14

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegR
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegH
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.isIntegralElt_add {K : Type} [Field K] [NumberField K] {x y : K} (hx : IsIntegralElt x)
    (hy : IsIntegralElt y) : IsIntegralElt (x + y) := by sorry

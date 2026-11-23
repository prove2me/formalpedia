-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_isIntegralElt_c
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.isIntegralElt_c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:44.382894+00:00
-- url     : https://prove2.me/theorems/1da65092-d510-42b1-897a-d1db41221065
-- title:
--   Semi Pt: is Integral Elt c
-- statement:
--   The Semi Pt construction uses the is Integral Elt c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegH.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegH.lean#L16-L19

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.isIntegralElt_c {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) {x : K}
    (hx : IsIntegralElt x) : IsIntegralElt (S.c x) := by sorry

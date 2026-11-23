-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wVal_outer
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.wVal_outer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:40.777802+00:00
-- url     : https://prove2.me/theorems/78efe439-67a6-4464-9229-18dcbc98edb6
-- title:
--   Semi Pt: w Val outer
-- statement:
--   The Semi Pt construction uses the w Val outer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegF.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegF.lean#L33-L36

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.wVal_outer {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i : Fin r)
    (h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m) : wVal r m g i = 1 := by sorry

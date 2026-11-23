-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wPart_mid
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.wPart_mid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:42.695104+00:00
-- url     : https://prove2.me/theorems/037d1319-5343-4281-8a3a-b7397603f798
-- title:
--   Semi Pt: w Part mid
-- statement:
--   The Semi Pt construction uses the w Part mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegF.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegF.lean#L28-L31

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.wPart_mid (r m : ℕ) (i : Fin r) (h : ¬ ((i : ℕ) < m ∨ r ≤ (i : ℕ) + m)) :
    wPart r m i = i := by sorry

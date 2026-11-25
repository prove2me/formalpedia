-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_colMat_mulVec
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.colMat_mulVec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:02:25.382835+00:00
-- url     : https://prove2.me/theorems/09fbb1f6-3b79-51ba-b35f-d5db2bb18ee1
-- title:
--   Semi Pt: col Mat mul Vec
-- statement:
--   The Semi Pt construction uses the col Mat mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegM.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegM.lean#L20-L23

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegM
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.colMat_mulVec {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) (t : Fin k → K) :
    colMat b *ᵥ t = ∑ j, t j • b j := by sorry

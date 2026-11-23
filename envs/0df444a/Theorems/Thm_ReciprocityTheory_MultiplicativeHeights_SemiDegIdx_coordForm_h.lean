-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_coordForm_h
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coordForm_h
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:11:05.584928+00:00
-- url     : https://prove2.me/theorems/80948158-6d6b-485d-ac6e-2aa446c64045
-- title:
--   Semi Deg Idx: coord Form h
-- statement:
--   The Semi Deg Idx construction uses the coord Form h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L42-L54

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coordForm_h {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) (s t : Fin k → K) :
    S.h (combMap b s) (combMap b t) = (coordForm S b).h s t := by sorry

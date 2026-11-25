-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_rows
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.hermForm_rows
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:00.065394+00:00
-- url     : https://prove2.me/theorems/b99526b7-4c21-4016-9731-91d908764d76
-- title:
--   Semi Deg Idx: herm Form rows
-- statement:
--   The Semi Deg Idx construction uses the herm Form rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCD.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCD.lean#L30-L34

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.hermForm_rows {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    (z : Fin k → Fin k → K) (i : Fin k) (v : Fin k → K) :
    S.h (z i) v = (((rowMat z).map S.c * S.G) *ᵥ v) i := by sorry

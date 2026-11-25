-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wittMat_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.wittMat_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:33.120237+00:00
-- url     : https://prove2.me/theorems/b52dae56-2e40-4cb9-ae3a-88f49f7def8e
-- title:
--   Semi Pt: witt Mat eq
-- statement:
--   The Semi Pt construction uses the witt Mat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegF.lean#L43-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegF.lean#L43-L61

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.wittMat_eq {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) :
    wittMat r m g = Matrix.of fun i j => if j = wPart r m i then wVal r m g i else 0 := by sorry

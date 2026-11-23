-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_det_gram_eq
-- name    : ReciprocityTheory.ReducedBases.T2.det_gram_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:05.750638+00:00
-- url     : https://prove2.me/theorems/bfd02591-5593-4364-9cd8-48620db38d9c
-- title:
--   T2: det gram eq
-- statement:
--   The T2 construction uses the det gram eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L29-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L29-L62

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix

theorem ReciprocityTheory.ReducedBases.T2.det_gram_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (v : Fin m → E) (hv : LinearIndependent ℝ v) :
    (Matrix.gram ℝ v).det = ∏ j, ‖gs v j‖ ^ 2 := by sorry

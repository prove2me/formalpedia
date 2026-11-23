-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_fB_apply
-- name    : ReciprocityTheory.ReducedBases.T2.fB_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:28.669907+00:00
-- url     : https://prove2.me/theorems/e0268fe0-b428-4dab-ad6e-8f3c168cdc02
-- title:
--   T2: f B apply
-- statement:
--   The T2 construction uses the f B apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L77-L78

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
variable {d : ℕ}

theorem ReciprocityTheory.ReducedBases.T2.fB_apply (B : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℤ) :
    fB B x = WithLp.toLp 2 (B *ᵥ toReal x) := by sorry

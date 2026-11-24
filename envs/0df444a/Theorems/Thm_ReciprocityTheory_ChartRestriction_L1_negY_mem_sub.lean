-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_negY_mem_sub
-- name    : ReciprocityTheory.ChartRestriction.L1.negY_mem_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:37:54.347714+00:00
-- url     : https://prove2.me/theorems/078575a5-5a81-451d-994c-37843fb23184
-- title:
--   L1: neg Y mem sub
-- statement:
--   The L1 construction uses the neg Y mem sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorSub.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorSub.lean#L17-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable {C : Type} [Field C] (K : Subfield C) (W : WeierstrassCurve C)

theorem ReciprocityTheory.ChartRestriction.L1.negY_mem_sub (hW : CoeffSub K W) {x y : C} (hx : x ∈ K) (hy : y ∈ K) :
    W.toAffine.negY x y ∈ K := by sorry

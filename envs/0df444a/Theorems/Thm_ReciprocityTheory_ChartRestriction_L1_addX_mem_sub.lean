-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_addX_mem_sub
-- name    : ReciprocityTheory.ChartRestriction.L1.addX_mem_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:37:27.447459+00:00
-- url     : https://prove2.me/theorems/41c7ce63-38e4-4e1e-bee1-f501e5ed0cf0
-- title:
--   L1: add X mem sub
-- statement:
--   The L1 construction uses the add X mem sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorSub.lean#L67-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorSub.lean#L67-L80

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

theorem ReciprocityTheory.ChartRestriction.L1.addX_mem_sub (hW : CoeffSub K W) {x₁ x₂ s : C} (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K)
    (hs : s ∈ K) : W.toAffine.addX x₁ x₂ s ∈ K := by sorry

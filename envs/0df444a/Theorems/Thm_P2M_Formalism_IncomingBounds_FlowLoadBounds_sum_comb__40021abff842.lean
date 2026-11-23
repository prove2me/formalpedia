-- Prove2me | Theorems.Thm_P2M_Formalism_IncomingBounds_FlowLoadBounds_sum_comb__40021abff842
-- name    : P2M_Formalism_IncomingBounds_FlowLoadBounds_sum_comb__40021abff842
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:20.54516+00:00
-- url     : https://prove2.me/theorems/cef76686-86aa-4f5e-b046-90d2d53a8606
-- title:
--   P2 M Formalism Incoming Bounds Flow Load Bounds sum comb  40021abff842: P2 M Formalism Incoming Bounds Flow Load Bounds sum comb  40021abff842
-- statement:
--   The P2 M Formalism Incoming Bounds Flow Load Bounds sum comb  40021abff842 construction uses the P2 M Formalism Incoming Bounds Flow Load Bounds sum comb  40021abff842 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L149-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L149-L151

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set
open scoped Pointwise
open Formalism Formalism.IncomingBounds
open Formalism.IncomingBounds.FlowLoadBounds
variable {l d : ℕ} [NeZero d]

theorem P2M_Formalism_IncomingBounds_FlowLoadBounds_sum_comb__40021abff842 {ι : Type*} (S : Finset ι) (f g : ι → ℝ) (a b : ℝ) :
    ∑ i ∈ S, (a * f i + b * g i) = a * ∑ i ∈ S, f i + b * ∑ i ∈ S, g i := by sorry

alias «Formalism».«IncomingBounds».«FlowLoadBounds».«sum_comb'» := P2M_Formalism_IncomingBounds_FlowLoadBounds_sum_comb__40021abff842

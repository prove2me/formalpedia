-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_trace_pow_eq_psumC
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.trace_pow_eq_psumC
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:43.290068+00:00
-- url     : https://prove2.me/theorems/a6fa8624-8820-4bec-a7a2-34248641d815
-- title:
--   Fib: trace pow eq psum C
-- statement:
--   The Fib construction uses the trace pow eq psum C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStC.lean#L267-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStC.lean#L267-L321

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open Polynomial IntermediateField

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.trace_pow_eq_psumC {K E : Type*} [Field K] [Field E] [Algebra K E] [CharZero K]
    [FiniteDimensional K E] {θ : E} (hθ : K⟮θ⟯ = ⊤) (j : ℕ) :
    Algebra.trace K E (θ ^ j) = psumC (minpoly K θ) (minpoly K θ).natDegree j := by sorry

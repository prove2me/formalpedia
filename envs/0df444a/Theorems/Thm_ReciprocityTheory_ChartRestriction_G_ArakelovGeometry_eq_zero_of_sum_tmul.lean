-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eq_zero_of_sum_tmul
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_zero_of_sum_tmul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:43.411937+00:00
-- url     : https://prove2.me/theorems/98f669da-0d06-5000-8c31-db657fa40467
-- title:
--   Arakelov Geometry: eq zero of sum tmul
-- statement:
--   The Arakelov Geometry construction uses the eq zero of sum tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStB.lean#L19-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStB.lean#L19-L40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Jacobson.Ring
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_zero_of_sum_tmul {Ω E : Type*} [Field Ω] [CharZero Ω] [Field E] [Algebra ℚ E] {r : ℕ}
    {s : Fin r → Ω} (hs : LinearIndependent ℚ s) {e : Fin r → E}
    (h : ∑ k, e k ⊗ₜ[ℚ] s k = 0) : e = 0 := by sorry

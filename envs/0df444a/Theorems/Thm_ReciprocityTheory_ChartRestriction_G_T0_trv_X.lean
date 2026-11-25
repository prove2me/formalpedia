-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_trv_X
-- name    : ReciprocityTheory.ChartRestriction.G.T0.trv_X
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:59.022164+00:00
-- url     : https://prove2.me/theorems/bc76634b-6db3-544d-8780-1db8ed3553a0
-- title:
--   T0: trv X
-- statement:
--   The T0 construction uses the trv X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RelationMapCommTransvection.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RelationMapCommTransvection.lean#L12-L17

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RelationMapCommTransvection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial

theorem ReciprocityTheory.ChartRestriction.G.T0.trv_X {R : Type*} [CommRing R] {D N : ℕ} (i k : Fin (D + 1))
    (e : Polynomial (MvPolynomial (TVar D N) R)) (t : TVar D N) :
    trv i k e (X t) = if t.1 = i then Polynomial.C (X t) + e * Polynomial.C (X (k, t.2))
      else Polynomial.C (X t) := by sorry

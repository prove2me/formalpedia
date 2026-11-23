-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sac_self
-- name    : ReciprocityTheory.ChartRestriction.G.T0.sac_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:52.22296+00:00
-- url     : https://prove2.me/theorems/68189932-d465-4f73-bd25-183b7b41d988
-- title:
--   T0: sac self
-- statement:
--   The T0 construction uses the sac self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SacSuccAbove.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SacSuccAbove.lean#L17-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
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

theorem ReciprocityTheory.ChartRestriction.G.T0.sac_self {β : Type*} {n : ℕ} (i : Fin (n + 1)) (x : β) (p : Fin n → β) :
    Fin.succAboveCases (α := fun _ => β) i x p i = x := by sorry

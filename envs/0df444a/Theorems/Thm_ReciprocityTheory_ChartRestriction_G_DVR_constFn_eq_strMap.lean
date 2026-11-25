-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_constFn_eq_strMap
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.constFn_eq_strMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:17:08.593854+00:00
-- url     : https://prove2.me/theorems/ef2bc3ef-2c9c-5ff8-a5fc-56a93e8e7ec6
-- title:
--   DVR: const Fn eq str Map
-- statement:
--   The DVR construction uses the const Fn eq str Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThickKer.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThickKer.lean#L14-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThickKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V : Type} [CommRing V] {X : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.DVR.constFn_eq_strMap (p : X ⟶ Sp V) (U : X.Opens) (a : V) : constFn p U a = strMap p U a := by sorry

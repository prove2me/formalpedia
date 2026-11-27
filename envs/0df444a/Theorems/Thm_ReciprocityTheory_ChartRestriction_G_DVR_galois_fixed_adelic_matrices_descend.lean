-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_galois_fixed_adelic_matrices_descend
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.galois_fixed_adelic_matrices_descend
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T06:26:07.166801+00:00
-- url     : https://prove2.me/theorems/98d28884-c7ff-5d4d-a4ab-138083a20f2f
-- title:
--   DVR: galois fixed adelic matrices descend
-- statement:
--   The DVR construction uses the galois fixed adelic matrices descend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PeriodicValuation.lean#L58-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PeriodicValuation.lean#L58-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ConstBFMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PeriodicValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm
open PeriodicValuation

theorem ReciprocityTheory.ChartRestriction.G.DVR.galois_fixed_adelic_matrices_descend (hL : Laws) (hTW : TWStatement) : FiniteOrderValuationInvariance := by sorry

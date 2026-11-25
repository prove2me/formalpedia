-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_fst_eq
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.exists_fst_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:56.654511+00:00
-- url     : https://prove2.me/theorems/9f016005-b8d4-5ed2-9d19-bb8b3fdce91a
-- title:
--   DVR: exists fst eq
-- statement:
--   The DVR construction uses the exists fst eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/NuExtA.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/NuExtA.lean#L76-L84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThickKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_NuExtA
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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {X : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.DVR.exists_fst_eq (p : X ⟶ Sp V) (J : Ideal V) {r : V} (hJ : J ≤ Ideal.span {r}) (x : X)
    (hx : r ∈ (p x).asIdeal) :
    ∃ x', pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' = x := by sorry

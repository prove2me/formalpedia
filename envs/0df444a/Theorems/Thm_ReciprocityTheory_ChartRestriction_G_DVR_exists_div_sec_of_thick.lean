-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_div_sec_of_thick
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.exists_div_sec_of_thick
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:24:47.317587+00:00
-- url     : https://prove2.me/theorems/bc2aa1a4-3474-5639-81b1-2af0bb47c62e
-- title:
--   DVR: exists div sec of thick
-- statement:
--   The DVR construction uses the exists div sec of thick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/NuExtA.lean#L86-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/NuExtA.lean#L86-L97

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.exists_div_sec_of_thick (p : X ⟶ Sp V) [Flat p] (J : Ideal V) {r : V} (hr : r ≠ 0)
    (hJ : J ≤ Ideal.span {r}) {M : LB X} (s : LB.Sec M)
    (h : ∀ j (x' : ↑(pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))),
      pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' ∈ M.U j →
      cst (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ p) x' r ∣
        gs (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) x' (M.U j) (s.f j)) :
    ∃ s' : LB.Sec M, ∀ j, s.f j = constFn p _ r * s'.f j := by sorry

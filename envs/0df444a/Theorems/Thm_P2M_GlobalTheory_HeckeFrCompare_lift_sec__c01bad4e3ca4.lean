-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HeckeFrCompare_lift_sec__c01bad4e3ca4
-- name    : P2M_GlobalTheory_HeckeFrCompare_lift_sec__c01bad4e3ca4
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:46:19.434897+00:00
-- url     : https://prove2.me/theorems/d8b60aa6-e43f-404c-ae57-43f313982791
-- title:
--   P2 M Global Theory Hecke Fr Compare lift sec  c01bad4e3ca4: P2 M Global Theory Hecke Fr Compare lift sec  c01bad4e3ca4
-- statement:
--   The P2 M Global Theory Hecke Fr Compare lift sec  c01bad4e3ca4 construction uses the P2 M Global Theory Hecke Fr Compare lift sec  c01bad4e3ca4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L129-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L129-L134

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {Ω : Type} [CommRing Ω]

theorem P2M_GlobalTheory_HeckeFrCompare_lift_sec__c01bad4e3ca4 (x : Sp Ω ⟶ Xo.X) {T : Scheme.{0}} {t : T ⟶ Sp Ω} (q : Sp Ω ⟶ T) (hq : q ≫ t = 𝟙 _)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (lift (𝟙 (Over.mk x)) (sec' x q hq ≫ a)).left = q ≫ toFib x t a := by sorry

alias «GlobalTheory».«HeckeFrCompare».«lift_sec'» := P2M_GlobalTheory_HeckeFrCompare_lift_sec__c01bad4e3ca4

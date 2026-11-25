-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HeckeFrCompare_sends_sec__iff_a2b331f1cbb6
-- name    : P2M_GlobalTheory_HeckeFrCompare_sends_sec__iff_a2b331f1cbb6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:45:18.410798+00:00
-- url     : https://prove2.me/theorems/6838fa85-630e-427b-b8a0-c76cd4756d4d
-- title:
--   P2 M Global Theory Hecke Fr Compare sends sec  iff a2b331f1cbb6: P2 M Global Theory Hecke Fr Compare sends sec  iff a2b331f1cbb6
-- statement:
--   The P2 M Global Theory Hecke Fr Compare sends sec  iff a2b331f1cbb6 construction uses the P2 M Global Theory Hecke Fr Compare sends sec  iff a2b331f1cbb6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L136-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L136-L141

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

theorem P2M_GlobalTheory_HeckeFrCompare_sends_sec__iff_a2b331f1cbb6 {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}
    (hψ : ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    {T : Scheme.{0}} {t : T ⟶ Sp Ω} (q : Sp Ω ⟶ T) (hq : q ≫ t = 𝟙 _)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) (b : Over.mk x' ⟶ Xo.univ.t.G) :
    Sends ψ (sec' x q hq ≫ a) b ↔ q ≫ push ψ t a = b.left := by sorry

alias «GlobalTheory».«HeckeFrCompare».«sends_sec'_iff» := P2M_GlobalTheory_HeckeFrCompare_sends_sec__iff_a2b331f1cbb6

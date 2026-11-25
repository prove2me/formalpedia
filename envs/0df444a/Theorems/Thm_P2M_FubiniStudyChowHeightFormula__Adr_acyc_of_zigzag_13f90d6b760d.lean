-- Prove2me | Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_acyc_of_zigzag_13f90d6b760d
-- name    : P2M_FubiniStudyChowHeightFormula__Adr_acyc_of_zigzag_13f90d6b760d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:08.388317+00:00
-- url     : https://prove2.me/theorems/538a44af-8f49-4df6-acfe-3f264f228002
-- title:
--   P2 M Fubini Study Chow Height Formula  Adr acyc of zigzag 13f90d6b760d: P2 M Fubini Study Chow Height Formula  Adr acyc of zigzag 13f90d6b760d
-- statement:
--   The P2 M Fubini Study Chow Height Formula  Adr acyc of zigzag 13f90d6b760d construction uses the P2 M Fubini Study Chow Height Formula  Adr acyc of zigzag 13f90d6b760d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L47-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L47-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_DividedPowerAlgebras_AcycOfCoprod
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
open CategoryTheory GlobalTheory.CatCoh
open FubiniStudyChowHeightFormula₂ FubiniStudyChowHeightFormula₂.Adr
universe v u v' u'
variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D]

theorem P2M_FubiniStudyChowHeightFormula__Adr_acyc_of_zigzag_13f90d6b760d (d : D) (h : Zigzag (𝟭 D) ((Functor.const D).obj d)) : Acyc R D := by sorry

alias «FubiniStudyChowHeightFormula₂».«Adr».«acyc_of_zigzag» := P2M_FubiniStudyChowHeightFormula__Adr_acyc_of_zigzag_13f90d6b760d

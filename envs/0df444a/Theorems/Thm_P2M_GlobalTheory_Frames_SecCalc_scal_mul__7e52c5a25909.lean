-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Frames_SecCalc_scal_mul__7e52c5a25909
-- name    : P2M_GlobalTheory_Frames_SecCalc_scal_mul__7e52c5a25909
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:18.602257+00:00
-- url     : https://prove2.me/theorems/3fdbec42-308c-44a7-b1cf-3f709ce73952
-- title:
--   P2 M Global Theory Frames Sec Calc scal mul  7e52c5a25909: P2 M Global Theory Frames Sec Calc scal mul  7e52c5a25909
-- statement:
--   The P2 M Global Theory Frames Sec Calc scal mul  7e52c5a25909 construction uses the P2 M Global Theory Frames Sec Calc scal mul  7e52c5a25909 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ScaledBaseChangeFibreSectionCalculus.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ScaledBaseChangeFibreSectionCalculus.lean#L24-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ScaledBaseChangeFibreSectionCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.SecCalc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem P2M_GlobalTheory_Frames_SecCalc_scal_mul__7e52c5a25909 {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by sorry

alias «GlobalTheory».«Frames».«SecCalc».«scal_mul'» := P2M_GlobalTheory_Frames_SecCalc_scal_mul__7e52c5a25909

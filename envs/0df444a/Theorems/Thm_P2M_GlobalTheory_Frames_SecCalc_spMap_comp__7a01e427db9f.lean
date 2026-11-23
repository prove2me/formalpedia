-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Frames_SecCalc_spMap_comp__7a01e427db9f
-- name    : P2M_GlobalTheory_Frames_SecCalc_spMap_comp__7a01e427db9f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:11.299854+00:00
-- url     : https://prove2.me/theorems/f79ee81b-667d-47d0-aa66-fbec9506ecbc
-- title:
--   P2 M Global Theory Frames Sec Calc sp Map comp  7a01e427db9f: P2 M Global Theory Frames Sec Calc sp Map comp  7a01e427db9f
-- statement:
--   The P2 M Global Theory Frames Sec Calc sp Map comp  7a01e427db9f construction uses the P2 M Global Theory Frames Sec Calc sp Map comp  7a01e427db9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ScaledBaseChangeFibreSectionCalculus.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ScaledBaseChangeFibreSectionCalculus.lean#L17-L19

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

theorem P2M_GlobalTheory_Frames_SecCalc_spMap_comp__7a01e427db9f {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by sorry

alias «GlobalTheory».«Frames».«SecCalc».«spMap_comp'» := P2M_GlobalTheory_Frames_SecCalc_spMap_comp__7a01e427db9f

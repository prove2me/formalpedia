-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HostModel_trForm_apply__9487e7fac180
-- name    : P2M_GlobalTheory_HostModel_trForm_apply__9487e7fac180
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:38:34.390801+00:00
-- url     : https://prove2.me/theorems/b3f1d090-b127-465b-8ec9-c4b808009161
-- title:
--   P2 M Global Theory Host Model tr Form apply  9487e7fac180: P2 M Global Theory Host Model tr Form apply  9487e7fac180
-- statement:
--   The P2 M Global Theory Host Model tr Form apply  9487e7fac180 construction uses the P2 M Global Theory Host Model tr Form apply  9487e7fac180 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/TrFormBaseChangeNondegenerate.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/TrFormBaseChangeNondegenerate.lean#L25-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem P2M_GlobalTheory_HostModel_trForm_apply__9487e7fac180 (H : Host E) (x y : 𝓞 E) : trForm H x y = Algebra.trace ℤ (𝓞 E) (x * H.bar y) := by sorry

alias «GlobalTheory».«HostModel».«trForm_apply'» := P2M_GlobalTheory_HostModel_trForm_apply__9487e7fac180

-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TensorLat_Hf_actE_cc__4d428fdd4074
-- name    : P2M_GlobalTheory_TensorLat_Hf_actE_cc__4d428fdd4074
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:29:46.262647+00:00
-- url     : https://prove2.me/theorems/e46a5dcc-d19d-4615-8362-327d02660b49
-- title:
--   P2 M Global Theory Tensor Lat Hf act E cc  4d428fdd4074: P2 M Global Theory Tensor Lat Hf act E cc  4d428fdd4074
-- statement:
--   The P2 M Global Theory Tensor Lat Hf act E cc  4d428fdd4074 construction uses the P2 M Global Theory Tensor Lat Hf act E cc  4d428fdd4074 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/FlatMemLatIffStdLat.lean#L230-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/FlatMemLatIffStdLat.lean#L230-L231

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
noncomputable section
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable [IsCMField E]

theorem P2M_GlobalTheory_TensorLat_Hf_actE_cc__4d428fdd4074 (α : E) (v w : Vsp dim) : Hf v (actE α w) = Hf (actE (cc α) v) w := by sorry

alias «GlobalTheory».«TensorLat».«Hf_actE_cc'» := P2M_GlobalTheory_TensorLat_Hf_actE_cc__4d428fdd4074

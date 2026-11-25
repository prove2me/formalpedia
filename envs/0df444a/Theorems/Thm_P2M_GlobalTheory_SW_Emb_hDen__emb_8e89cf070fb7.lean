-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_Emb_hDen__emb_8e89cf070fb7
-- name    : P2M_GlobalTheory_SW_Emb_hDen__emb_8e89cf070fb7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:17.37297+00:00
-- url     : https://prove2.me/theorems/32693870-5130-4cc4-96f4-831b01a1dfc2
-- title:
--   P2 M Global Theory SW Emb h Den  emb 8e89cf070fb7: P2 M Global Theory SW Emb h Den  emb 8e89cf070fb7
-- statement:
--   The P2 M Global Theory SW Emb h Den  emb 8e89cf070fb7 construction uses the P2 M Global Theory SW Emb h Den  emb 8e89cf070fb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EmbeddingCompatibleWithWeilAndDenominator.lean#L208-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EmbeddingCompatibleWithWeilAndDenominator.lean#L208-L211

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
omit [NumberField E] [IsCMField E]

theorem P2M_GlobalTheory_SW_Emb_hDen__emb_8e89cf070fb7 (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (τ : Ψ) :
    hDen' Ψ (emb γ) (corZ s Z) τ = cor 1 (hDen' Ψ γ Z τ) := by sorry

alias «GlobalTheory».«SW».«Emb».«hDen'_emb» := P2M_GlobalTheory_SW_Emb_hDen__emb_8e89cf070fb7

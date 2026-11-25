-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HostModel_arcIn_D__fa63146f2c1d
-- name    : P2M_GlobalTheory_HostModel_arcIn_D__fa63146f2c1d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:22:41.056158+00:00
-- url     : https://prove2.me/theorems/a2585e1b-50c7-464a-8c5a-0df6cf0747bb
-- title:
--   P2 M Global Theory Host Model arc In D  fa63146f2c1d: P2 M Global Theory Host Model arc In D  fa63146f2c1d
-- statement:
--   The P2 M Global Theory Host Model arc In D  fa63146f2c1d construction uses the P2 M Global Theory Host Model arc In D  fa63146f2c1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/IsPrimitiveRootArcRoot.lean#L298-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/IsPrimitiveRootArcRoot.lean#L298-L298

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ZeroFLeftExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HostModel
open ToricData ConjDual
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : Host E} {l : Level H} (c : Coeff l) (k : Type) [CommRing k] [IsDomain k] (bF : c.F →+* k)

theorem P2M_GlobalTheory_HostModel_arcIn_D__fa63146f2c1d : (arcIn c k bF).D₀ = toricPre k (𝓞 E) fun _ => 1 := by sorry

alias «GlobalTheory».«HostModel».«arcIn_D₀» := P2M_GlobalTheory_HostModel_arcIn_D__fa63146f2c1d

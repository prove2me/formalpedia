-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CongGrp_pow_mem__de67754d33b0
-- name    : P2M_GlobalTheory_CongGrp_pow_mem__de67754d33b0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:22:49.486347+00:00
-- url     : https://prove2.me/theorems/7e1973dc-8f76-45fc-841a-9d36ca34d088
-- title:
--   P2 M Global Theory Cong Grp pow mem  de67754d33b0: P2 M Global Theory Cong Grp pow mem  de67754d33b0
-- statement:
--   The P2 M Global Theory Cong Grp pow mem  de67754d33b0 construction uses the P2 M Global Theory Cong Grp pow mem  de67754d33b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MatrixCongruentOneModUniformizerPowGroupAndOrbit.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MatrixCongruentOneModUniformizerPowGroupAndOrbit.lean#L111-L113

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.CongGrp
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem P2M_GlobalTheory_CongGrp_pow_mem__de67754d33b0 (L : LocE F E) (ϖ : 𝒪[F]) (i : ℕ) : algebraMap F E ((ϖ : F) ^ i) ∈ L.O := by sorry

alias «GlobalTheory».«CongGrp».«pow_mem'» := P2M_GlobalTheory_CongGrp_pow_mem__de67754d33b0

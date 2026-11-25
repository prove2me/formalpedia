-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Reg_TrivBound_vV_zero__17b3298cc3dd
-- name    : P2M_GlobalTheory_Reg_TrivBound_vV_zero__17b3298cc3dd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:49.657963+00:00
-- url     : https://prove2.me/theorems/53cf7667-503c-4c23-8f23-01496e561406
-- title:
--   P2 M Global Theory Reg Triv Bound v V zero  17b3298cc3dd: P2 M Global Theory Reg Triv Bound v V zero  17b3298cc3dd
-- statement:
--   The P2 M Global Theory Reg Triv Bound v V zero  17b3298cc3dd construction uses the P2 M Global Theory Reg Triv Bound v V zero  17b3298cc3dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/CombinedBoundAtTrivialValuationsOfCharts.lean#L246-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/CombinedBoundAtTrivialValuationsOfCharts.lean#L246-L248

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_CombinedBoundAtTrivialValuationsOfCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.TrivBound
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg

theorem P2M_GlobalTheory_Reg_TrivBound_vV_zero__17b3298cc3dd {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    vV (K' := FractionRing V) V 0 = 0 := by sorry

alias «GlobalTheory».«Reg».«TrivBound».«vV_zero'» := P2M_GlobalTheory_Reg_TrivBound_vV_zero__17b3298cc3dd

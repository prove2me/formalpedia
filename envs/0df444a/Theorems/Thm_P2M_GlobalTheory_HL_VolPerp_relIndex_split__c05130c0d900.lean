-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_VolPerp_relIndex_split__c05130c0d900
-- name    : P2M_GlobalTheory_HL_VolPerp_relIndex_split__c05130c0d900
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:56:29.382018+00:00
-- url     : https://prove2.me/theorems/f8cabc2b-7298-4884-92f4-4b1c1600bb8c
-- title:
--   P2 M Global Theory HL Vol Perp rel Index split  c05130c0d900: P2 M Global Theory HL Vol Perp rel Index split  c05130c0d900
-- statement:
--   The P2 M Global Theory HL Vol Perp rel Index split  c05130c0d900 construction uses the P2 M Global Theory HL Vol Perp rel Index split  c05130c0d900 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfDualHermitianLatticeTraceOrthogonalVolumeRat.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfDualHermitianLatticeTraceOrthogonalVolumeRat.lean#L25-L32

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualHermitianLatticeTraceOrthogonalVolumeRat
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.VolPerp
open GlobalTheory.HL.DualInter

theorem P2M_GlobalTheory_HL_VolPerp_relIndex_split__c05130c0d900 {G : Type} [AddCommGroup G] (A B Z : AddSubgroup G) :
    B.relIndex A = (B ⊓ Z).relIndex (A ⊓ Z) *
      (((A ⊓ B) ⊔ Z).relIndex ((A ⊔ Z) ⊓ (B ⊔ Z)) * (B ⊔ Z).relIndex (A ⊔ Z)) := by sorry

alias «GlobalTheory».«HL».«VolPerp».«relIndex_split'» := P2M_GlobalTheory_HL_VolPerp_relIndex_split__c05130c0d900

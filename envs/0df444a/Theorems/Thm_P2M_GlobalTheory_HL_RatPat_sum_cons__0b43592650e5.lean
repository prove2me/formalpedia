-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_RatPat_sum_cons__0b43592650e5
-- name    : P2M_GlobalTheory_HL_RatPat_sum_cons__0b43592650e5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:25.194603+00:00
-- url     : https://prove2.me/theorems/2a9f6bdc-7a07-5042-a374-a4de1e6e7293
-- title:
--   P2 M Global Theory HL Rat Pat sum cons  0b43592650e5: P2 M Global Theory HL Rat Pat sum cons  0b43592650e5
-- statement:
--   The P2 M Global Theory HL Rat Pat sum cons  0b43592650e5 construction uses the P2 M Global Theory HL Rat Pat sum cons  0b43592650e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BlockUnitriangularRationalFromCommonStabiliser.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BlockUnitriangularRationalFromCommonStabiliser.lean#L19-L21

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianStabiliserRationalUnitriangularPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BlockUnitriangularRationalFromCommonStabiliser
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatPat

theorem P2M_GlobalTheory_HL_RatPat_sum_cons__0b43592650e5 {R : Type} [CommRing R] (t : Rˣ) (s : ℕ+) (bs : List (Rˣ × ℕ+)) :
    (((t, s) :: bs).map (fun b => (b.2 : ℕ))).sum = (s : ℕ) + (bs.map (fun b => (b.2 : ℕ))).sum := by sorry

alias «GlobalTheory».«HL».«RatPat».«sum_cons'» := P2M_GlobalTheory_HL_RatPat_sum_cons__0b43592650e5

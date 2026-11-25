-- Prove2me | Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_isHW_zero__e607ce74737d
-- name    : P2M_Formalism_CountingSumsFrames_TO_isHW_zero__e607ce74737d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:21.875071+00:00
-- url     : https://prove2.me/theorems/4200ae59-1ec5-4967-9f53-6045b5fe7162
-- title:
--   P2 M Formalism Counting Sums Frames TO is HW zero  e607ce74737d: P2 M Formalism Counting Sums Frames TO is HW zero  e607ce74737d
-- statement:
--   The P2 M Formalism Counting Sums Frames TO is HW zero  e607ce74737d construction uses the P2 M Formalism Counting Sums Frames TO is HW zero  e607ce74737d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3099-L3102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3099-L3102

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem P2M_Formalism_CountingSumsFrames_TO_isHW_zero__e607ce74737d (L : Letters N) (j : ℕ) (la : Fin r → ℤ) :
    (GA p L j).IsHW la (0 : MvPolynomial (Fin N × Fin r) ℚ_[p]) := by sorry

alias «Formalism».«CountingSumsFrames».«TO».«isHW_zero'» := P2M_Formalism_CountingSumsFrames_TO_isHW_zero__e607ce74737d

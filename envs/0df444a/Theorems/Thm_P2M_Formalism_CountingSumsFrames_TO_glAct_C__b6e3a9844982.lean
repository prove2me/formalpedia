-- Prove2me | Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_glAct_C__b6e3a9844982
-- name    : P2M_Formalism_CountingSumsFrames_TO_glAct_C__b6e3a9844982
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:09.510372+00:00
-- url     : https://prove2.me/theorems/9334f90e-b493-4236-a75d-5d2b52e775dd
-- title:
--   P2 M Formalism Counting Sums Frames TO gl Act C  b6e3a9844982: P2 M Formalism Counting Sums Frames TO gl Act C  b6e3a9844982
-- statement:
--   The P2 M Formalism Counting Sums Frames TO gl Act C  b6e3a9844982 construction uses the P2 M Formalism Counting Sums Frames TO gl Act C  b6e3a9844982 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1991-L1995
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1991-L1995

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
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem P2M_Formalism_CountingSumsFrames_TO_glAct_C__b6e3a9844982 (L : Letters N) (j : ℕ) (c d : Fin r) (a : ℚ_[p]) :
    glAct p L j c d (C a) = 0 := by sorry

alias «Formalism».«CountingSumsFrames».«TO».«glAct_C'» := P2M_Formalism_CountingSumsFrames_TO_glAct_C__b6e3a9844982

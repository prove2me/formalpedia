-- Prove2me | Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_tiePhi_mem__82f9fe5d1504
-- name    : P2M_Formalism_CountingSumsFrames_TO_tiePhi_mem__82f9fe5d1504
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:32.460033+00:00
-- url     : https://prove2.me/theorems/89d88160-a1aa-4b10-b352-b96ffd1db936
-- title:
--   P2 M Formalism Counting Sums Frames TO tie Phi mem  82f9fe5d1504: P2 M Formalism Counting Sums Frames TO tie Phi mem  82f9fe5d1504
-- statement:
--   The P2 M Formalism Counting Sums Frames TO tie Phi mem  82f9fe5d1504 construction uses the P2 M Formalism Counting Sums Frames TO tie Phi mem  82f9fe5d1504 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1374-L1385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1374-L1385

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
variable {k σ : Type} [Field k]

theorem P2M_Formalism_CountingSumsFrames_TO_tiePhi_mem__82f9fe5d1504 {r : ℕ} (w e : Fin r → σ) (o n z : ℕ) :
    (Formalism.GM.tiePhi w e o n z : Module.End k (MvPolynomial σ k)) ∈ FockB.Ops (Set.range w ∪ Set.range e) := by sorry

alias «Formalism».«CountingSumsFrames».«TO».«tiePhi_mem'» := P2M_Formalism_CountingSumsFrames_TO_tiePhi_mem__82f9fe5d1504

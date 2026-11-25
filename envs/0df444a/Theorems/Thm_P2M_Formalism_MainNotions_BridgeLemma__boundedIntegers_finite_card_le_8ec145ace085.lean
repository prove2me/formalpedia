-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__boundedIntegers_finite_card_le_8ec145ace085
-- name    : P2M_Formalism_MainNotions_BridgeLemma__boundedIntegers_finite_card_le_8ec145ace085
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:00:19.630237+00:00
-- url     : https://prove2.me/theorems/f3c0a9e7-fe2b-424f-8aa3-312dd437d286
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  bounded Integers finite card le 8ec145ace085: P2 M Formalism Main Notions Bridge Lemma  bounded Integers finite card le 8ec145ace085
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  bounded Integers finite card le 8ec145ace085 construction uses the P2 M Formalism Main Notions Bridge Lemma  bounded Integers finite card le 8ec145ace085 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L32-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L32-L58

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Formalism.HermitianLatticesTheory Module
variable (K : Type) [Field K] [NumberField K]

theorem P2M_Formalism_MainNotions_BridgeLemma__boundedIntegers_finite_card_le_8ec145ace085 (B : ℝ) (hB : 0 < B) :
    (boundedIntegers K B).Finite ∧ ((boundedIntegers K B).ncard : ℝ) ≤ (1 + 2 * B) ^ (2 * finrank ℚ K) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«boundedIntegers_finite_card_le» := P2M_Formalism_MainNotions_BridgeLemma__boundedIntegers_finite_card_le_8ec145ace085

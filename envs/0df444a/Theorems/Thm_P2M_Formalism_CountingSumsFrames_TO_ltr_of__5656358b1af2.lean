-- Prove2me | Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_ltr_of__5656358b1af2
-- name    : P2M_Formalism_CountingSumsFrames_TO_ltr_of__5656358b1af2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:53.245925+00:00
-- url     : https://prove2.me/theorems/633ef2d8-4905-40b1-ba2c-cb9cb34390dc
-- title:
--   P2 M Formalism Counting Sums Frames TO ltr of  5656358b1af2: P2 M Formalism Counting Sums Frames TO ltr of  5656358b1af2
-- statement:
--   The P2 M Formalism Counting Sums Frames TO ltr of  5656358b1af2 construction uses the P2 M Formalism Counting Sums Frames TO ltr of  5656358b1af2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L510-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L510-L519

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
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

theorem P2M_Formalism_CountingSumsFrames_TO_ltr_of__5656358b1af2 {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → ¬ fs v) : ltr fs m = m := by sorry

alias «Formalism».«CountingSumsFrames».«TO».«ltr_of'» := P2M_Formalism_CountingSumsFrames_TO_ltr_of__5656358b1af2

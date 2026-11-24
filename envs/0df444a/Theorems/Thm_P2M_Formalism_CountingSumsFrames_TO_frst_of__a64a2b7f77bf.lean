-- Prove2me | Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_frst_of__a64a2b7f77bf
-- name    : P2M_Formalism_CountingSumsFrames_TO_frst_of__a64a2b7f77bf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:40.181279+00:00
-- url     : https://prove2.me/theorems/f1541138-71cc-4f0d-b091-2b14e72ea825
-- title:
--   P2 M Formalism Counting Sums Frames TO frst of  a64a2b7f77bf: P2 M Formalism Counting Sums Frames TO frst of  a64a2b7f77bf
-- statement:
--   The P2 M Formalism Counting Sums Frames TO frst of  a64a2b7f77bf construction uses the P2 M Formalism Counting Sums Frames TO frst of  a64a2b7f77bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L502-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L502-L509

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

theorem P2M_Formalism_CountingSumsFrames_TO_frst_of__a64a2b7f77bf {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → ¬ fs v) : frst fs m = 0 := by sorry

alias «Formalism».«CountingSumsFrames».«TO».«frst_of'» := P2M_Formalism_CountingSumsFrames_TO_frst_of__a64a2b7f77bf

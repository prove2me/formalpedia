-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__natAbs_norm_le_pow_of_bounded_b1a71d5dc224
-- name    : P2M_Formalism_MainNotions_BridgeLemma__natAbs_norm_le_pow_of_bounded_b1a71d5dc224
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:32.63082+00:00
-- url     : https://prove2.me/theorems/061a53fd-f7ab-440b-b281-b62c4db5c918
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  nat Abs norm le pow of bounded b1a71d5dc224: P2 M Formalism Main Notions Bridge Lemma  nat Abs norm le pow of bounded b1a71d5dc224
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  nat Abs norm le pow of bounded b1a71d5dc224 construction uses the P2 M Formalism Main Notions Bridge Lemma  nat Abs norm le pow of bounded b1a71d5dc224 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L268-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L268-L277

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

theorem P2M_Formalism_MainNotions_BridgeLemma__natAbs_norm_le_pow_of_bounded_b1a71d5dc224 (K : Type) [Field K] [NumberField K] (d : 𝓞 K) (B : ℝ)
    (hd : ∀ φ : K →+* ℂ, ‖φ (d : K)‖ ≤ B) : ((Algebra.norm ℤ d).natAbs : ℝ) ≤ B ^ finrank ℚ K := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«natAbs_norm_le_pow_of_bounded» := P2M_Formalism_MainNotions_BridgeLemma__natAbs_norm_le_pow_of_bounded_b1a71d5dc224

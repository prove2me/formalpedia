-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__exists_small_mem_fractional_ideal_90c2b6906406
-- name    : P2M_Formalism_MainNotions_BridgeLemma__exists_small_mem_fractional_ideal_90c2b6906406
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:20.408463+00:00
-- url     : https://prove2.me/theorems/5df2db75-fd4b-435c-b88f-62237d89fe46
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  exists small mem fractional ideal 90c2b6906406: P2 M Formalism Main Notions Bridge Lemma  exists small mem fractional ideal 90c2b6906406
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  exists small mem fractional ideal 90c2b6906406 construction uses the P2 M Formalism Main Notions Bridge Lemma  exists small mem fractional ideal 90c2b6906406 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L30-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L30-L88

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal
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
open NumberField NumberField.mixedEmbedding Formalism.HermitianLatticesTheory
open scoped nonZeroDivisors NNReal ENNReal
open scoped Classical

theorem P2M_Formalism_MainNotions_BridgeLemma__exists_small_mem_fractional_ideal_90c2b6906406 (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hI : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, (w a) ^ 2 ≤ rootDiscriminant K := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«exists_small_mem_fractional_ideal» := P2M_Formalism_MainNotions_BridgeLemma__exists_small_mem_fractional_ideal_90c2b6906406

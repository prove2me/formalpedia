-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__star_mem_integers_6f5fb9ce5b0a
-- name    : P2M_Formalism_MainNotions_BridgeLemma__star_mem_integers_6f5fb9ce5b0a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:09.564774+00:00
-- url     : https://prove2.me/theorems/8dede8ce-d8a8-486e-88d6-874ba5af291c
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  star mem integers 6f5fb9ce5b0a: P2 M Formalism Main Notions Bridge Lemma  star mem integers 6f5fb9ce5b0a
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  star mem integers 6f5fb9ce5b0a construction uses the P2 M Formalism Main Notions Bridge Lemma  star mem integers 6f5fb9ce5b0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L176-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L176-L181

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

theorem P2M_Formalism_MainNotions_BridgeLemma__star_mem_integers_6f5fb9ce5b0a {K : Type} [Field K] [NumberField K] [StarRing K] {a : K}
    (ha : a ∈ Set.range (algebraMap (𝓞 K) K)) : star a ∈ Set.range (algebraMap (𝓞 K) K) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«star_mem_integers» := P2M_Formalism_MainNotions_BridgeLemma__star_mem_integers_6f5fb9ce5b0a

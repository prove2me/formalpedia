-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rootDiscr_pow_eq_sqrt_discr_9399e9c24fe2
-- name    : P2M_Formalism_MainNotions_BridgeLemma__rootDiscr_pow_eq_sqrt_discr_9399e9c24fe2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:40.266037+00:00
-- url     : https://prove2.me/theorems/8c726356-873f-466a-acd2-bd5763973bb8
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  root Discr pow eq sqrt discr 9399e9c24fe2: P2 M Formalism Main Notions Bridge Lemma  root Discr pow eq sqrt discr 9399e9c24fe2
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  root Discr pow eq sqrt discr 9399e9c24fe2 construction uses the P2 M Formalism Main Notions Bridge Lemma  root Discr pow eq sqrt discr 9399e9c24fe2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L11-L24

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

theorem P2M_Formalism_MainNotions_BridgeLemma__rootDiscr_pow_eq_sqrt_discr_9399e9c24fe2 (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    rootDiscriminant K ^ InfinitePlace.nrComplexPlaces K = Real.sqrt |(discr K : ℝ)| := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«rootDiscr_pow_eq_sqrt_discr» := P2M_Formalism_MainNotions_BridgeLemma__rootDiscr_pow_eq_sqrt_discr_9399e9c24fe2

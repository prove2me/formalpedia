-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__norm_embedding_le_trace_44957880a079
-- name    : P2M_Formalism_MainNotions_BridgeLemma__norm_embedding_le_trace_44957880a079
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:53.230803+00:00
-- url     : https://prove2.me/theorems/d6390c9b-91e8-40ad-97ae-644dadcc86d1
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  norm embedding le trace 44957880a079: P2 M Formalism Main Notions Bridge Lemma  norm embedding le trace 44957880a079
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  norm embedding le trace 44957880a079 construction uses the P2 M Formalism Main Notions Bridge Lemma  norm embedding le trace 44957880a079 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L16-L29

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair
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
open NumberField Module Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_MainNotions_BridgeLemma__norm_embedding_le_trace_44957880a079 (a : K) (ha : ∀ σ : K →ₐ[ℚ] ℂ, ∃ r : ℝ, 0 ≤ r ∧ σ a = (r : ℂ)) (φ : K →+* ℂ) :
    ‖φ a‖ ≤ ((Algebra.trace ℚ K a : ℚ) : ℝ) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«norm_embedding_le_trace» := P2M_Formalism_MainNotions_BridgeLemma__norm_embedding_le_trace_44957880a079

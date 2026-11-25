-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__short_vector_every_place_61a50f9129ad
-- name    : P2M_Formalism_MainNotions_BridgeLemma__short_vector_every_place_61a50f9129ad
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:00:18.819236+00:00
-- url     : https://prove2.me/theorems/3c7c9236-7c25-4b23-b3cf-ae68ee3ca56d
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  short vector every place 61a50f9129ad: P2 M Formalism Main Notions Bridge Lemma  short vector every place 61a50f9129ad
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  short vector every place 61a50f9129ad construction uses the P2 M Formalism Main Notions Bridge Lemma  short vector every place 61a50f9129ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L280-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L280-L315

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

theorem P2M_Formalism_MainNotions_BridgeLemma__short_vector_every_place_61a50f9129ad (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) :
    ShortVectorEveryPlace K (2 * (finrank ℚ K : ℝ) * rootDiscriminant K) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«short_vector_every_place» := P2M_Formalism_MainNotions_BridgeLemma__short_vector_every_place_61a50f9129ad

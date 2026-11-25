-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__exists_short_vector_minkowski_88a123bac9a8
-- name    : P2M_Formalism_MainNotions_BridgeLemma__exists_short_vector_minkowski_88a123bac9a8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:00:27.633983+00:00
-- url     : https://prove2.me/theorems/1bac1a1d-6183-436e-9b36-6a18b930691d
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  exists short vector minkowski 88a123bac9a8: P2 M Formalism Main Notions Bridge Lemma  exists short vector minkowski 88a123bac9a8
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  exists short vector minkowski 88a123bac9a8 construction uses the P2 M Formalism Main Notions Bridge Lemma  exists short vector minkowski 88a123bac9a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L252-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L252-L276

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
open MeasureTheory

theorem P2M_Formalism_MainNotions_BridgeLemma__exists_short_vector_minkowski_88a123bac9a8 (N : ℕ) (hN : 1 ≤ N) (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin N))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (R : ℝ) (hR : 0 ≤ R)
    (hvol : ZLattice.covolume Λ * 2 ^ N < R ^ N * (√Real.pi ^ N / Real.Gamma ((N : ℝ) / 2 + 1))) :
    ∃ v ∈ Λ, v ≠ 0 ∧ ‖v‖ < R := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«exists_short_vector_minkowski» := P2M_Formalism_MainNotions_BridgeLemma__exists_short_vector_minkowski_88a123bac9a8

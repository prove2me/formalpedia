-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__mass_le_of_card_class_reps_le_c99329ec7ab7
-- name    : P2M_Formalism_MainNotions_BridgeLemma__mass_le_of_card_class_reps_le_c99329ec7ab7
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:45.187701+00:00
-- url     : https://prove2.me/theorems/27032c34-a694-4308-a213-554aacabe09d
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  mass le of card class reps le c99329ec7ab7: P2 M Formalism Main Notions Bridge Lemma  mass le of card class reps le c99329ec7ab7
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  mass le of card class reps le c99329ec7ab7 construction uses the P2 M Formalism Main Notions Bridge Lemma  mass le of card class reps le c99329ec7ab7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/GenusOrthonormalIntegralUnimodular.lean#L76-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/GenusOrthonormalIntegralUnimodular.lean#L76-L88

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_GenusOrthonormalIntegralUnimodular
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
open NumberField Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem P2M_Formalism_MainNotions_BridgeLemma__mass_le_of_card_class_reps_le_c99329ec7ab7 (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ s, Formalism.ThetaLiftIndependence.IsClassReps h L s → (s.card : ℝ) ≤ B) : mass h L ≤ B := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«mass_le_of_card_class_reps_le» := P2M_Formalism_MainNotions_BridgeLemma__mass_le_of_card_class_reps_le_c99329ec7ab7

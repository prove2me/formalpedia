-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_nhds_zero_finiteAdele_2c19578e73bc
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_nhds_zero_finiteAdele_2c19578e73bc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:00.482395+00:00
-- url     : https://prove2.me/theorems/43701042-14a2-41c8-8e0a-32c8e8ab8a07
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods nhds zero finite Adele 2c19578e73bc: P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods nhds zero finite Adele 2c1957
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods nhds zero finite Adele 2c19578e73bc construction uses the P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods nhds zero finite Adele 2c19578e73bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L20-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L20-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAENeighbourhoods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_nhds_zero_finiteAdele_2c19578e73bc {W : Set (FiniteAdeleRing (𝓞 F) F)} (hW : W ∈ 𝓝 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ x : FiniteAdeleRing (𝓞 F) F,
      (∀ v ∈ S, x v = 0) → (∀ v ∉ S, x v ∈ v.adicCompletionIntegers F) → x ∈ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«AENeighbourhoods».«nhds_zero_finiteAdele» := P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_nhds_zero_finiteAdele_2c19578e73bc

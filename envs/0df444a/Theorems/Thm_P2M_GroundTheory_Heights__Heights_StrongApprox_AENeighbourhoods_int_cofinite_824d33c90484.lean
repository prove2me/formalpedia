-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_int_cofinite_824d33c90484
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_int_cofinite_824d33c90484
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:06.415779+00:00
-- url     : https://prove2.me/theorems/283c4920-c316-4857-9eac-510615fccc0f
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods int cofinite 824d33c90484: P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods int cofinite 824d33c90484
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods int cofinite 824d33c90484 construction uses the P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods int cofinite 824d33c90484 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L121-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L121-L131

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_int_cofinite_824d33c90484 (a : AE F E) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, compAt E v a ∈ intAt E v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«AENeighbourhoods».«int_cofinite» := P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_int_cofinite_824d33c90484

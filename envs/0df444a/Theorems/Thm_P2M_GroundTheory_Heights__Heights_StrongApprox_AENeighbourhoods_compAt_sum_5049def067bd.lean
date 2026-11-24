-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_compAt_sum_5049def067bd
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_compAt_sum_5049def067bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:39.68483+00:00
-- url     : https://prove2.me/theorems/6d6abda1-b52f-4ab7-b7ed-93d1b96506d3
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods comp At sum 5049def067bd: P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods comp At sum 5049def067bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods comp At sum 5049def067bd construction uses the P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods comp At sum 5049def067bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L70-L73

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_compAt_sum_5049def067bd (v : HeightOneSpectrum (𝓞 F))
    (X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F) :
    compAt E v (∑ l, X l ⊗ₜ[F] intBasis E l) = ∑ l, X l v ⊗ₜ[F] intBasis E l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«AENeighbourhoods».«compAt_sum» := P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_compAt_sum_5049def067bd

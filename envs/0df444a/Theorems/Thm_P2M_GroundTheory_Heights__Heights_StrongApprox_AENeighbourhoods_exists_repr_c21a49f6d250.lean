-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_exists_repr_c21a49f6d250
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_exists_repr_c21a49f6d250
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:13.904588+00:00
-- url     : https://prove2.me/theorems/29dc7eab-bef0-4cc8-bd60-c0676d4c5b7d
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods exists repr c21a49f6d250: P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods exists repr c21a49f6d250
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods exists repr c21a49f6d250 construction uses the P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods exists repr c21a49f6d250 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L75-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L75-L90

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_exists_repr_c21a49f6d250 (a : AE F E) :
    ∃ X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F,
      a = ∑ l, X l ⊗ₜ[F] intBasis E l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«AENeighbourhoods».«exists_repr» := P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_exists_repr_c21a49f6d250

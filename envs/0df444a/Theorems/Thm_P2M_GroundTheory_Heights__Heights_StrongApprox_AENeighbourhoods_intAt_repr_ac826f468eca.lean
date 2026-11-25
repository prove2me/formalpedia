-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_intAt_repr_ac826f468eca
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_intAt_repr_ac826f468eca
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:43.646601+00:00
-- url     : https://prove2.me/theorems/f7622ed4-5ad4-53e5-8c14-0cbd7e790e1c
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods int At repr ac826f468eca: P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods int At repr ac826f468eca
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods int At repr ac826f468eca construction uses the P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods int At repr ac826f468eca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L49-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L49-L68

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_intAt_repr_ac826f468eca (v : HeightOneSpectrum (𝓞 F)) {z : Kv E v} (hz : z ∈ intAt E v) :
    ∃ y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F,
      (∀ l, y l ∈ v.adicCompletionIntegers F) ∧ z = ∑ l, y l ⊗ₜ[F] intBasis E l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«AENeighbourhoods».«intAt_repr» := P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_intAt_repr_ac826f468eca

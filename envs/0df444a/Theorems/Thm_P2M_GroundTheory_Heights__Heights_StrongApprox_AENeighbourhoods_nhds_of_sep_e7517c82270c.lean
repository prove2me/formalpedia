-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_nhds_of_sep_e7517c82270c
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_nhds_of_sep_e7517c82270c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:49.277389+00:00
-- url     : https://prove2.me/theorems/36e6ef8c-f943-5a8a-8152-b195bcbb2059
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods nhds of sep e7517c82270c: P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods nhds of sep e7517c82270c
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods nhds of sep e7517c82270c construction uses the P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods nhds of sep e7517c82270c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L133-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L133-L166

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_nhds_of_sep_e7517c82270c [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)]
    (hsep : ∀ a b : AE F E, (∀ v, compAt E v a = compAt E v b) → a = b) (N : ℕ)
    (U : Set (Matrix (Fin N) (Fin N) (AE F E))) (hU : U ∈ 𝓝 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ M : Matrix (Fin N) (Fin N) (AE F E),
      (∀ i j, (∀ v ∈ S, compAt E v (M i j) = 0) ∧ ∀ v ∉ S, compAt E v (M i j) ∈ intAt E v) →
      M ∈ U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«AENeighbourhoods».«nhds_of_sep» := P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_nhds_of_sep_e7517c82270c

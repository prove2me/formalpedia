-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueBundles_hypotheses_inhabited_d52ffbd2fcda
-- name    : P2M_GroundTheory_Heights__Heights_Model_GlueBundles_hypotheses_inhabited_d52ffbd2fcda
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:08.461359+00:00
-- url     : https://prove2.me/theorems/da36b80a-2336-4cdb-9378-8a5351fd5049
-- title:
--   P2 M Ground Theory Heights  Heights Model Glue Bundles hypotheses inhabited d52ffbd2fcda: P2 M Ground Theory Heights  Heights Model Glue Bundles hypotheses inhabited d52ffbd2fcda
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Glue Bundles hypotheses inhabited d52ffbd2fcda construction uses the P2 M Ground Theory Heights  Heights Model Glue Bundles hypotheses inhabited d52ffbd2fcda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L557-L566
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L557-L566

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_GlueBundles_hypotheses_inhabited_d52ffbd2fcda :
    let S : Finset Nat.Primes := {⟨2, Nat.prime_two⟩}
    IsVectorBundle (structureModule (invOpen (𝟙 SpecZ) (primeProd S) : Scheme.{0})) ∧
      (∀ p : S, IsVectorBundle (structureModule (baseChange (𝟙 SpecZ) (ZLoc p)))) ∧
      ∀ p : S, Nonempty ((Scheme.Modules.pullback (ratToLoc (𝟙 SpecZ) p)).obj
        (structureModule (baseChange (𝟙 SpecZ) (ZLoc p))) ≅
        (Scheme.Modules.pullback (toInvOpen (𝟙 SpecZ) ℚ (primeProd S)
          (isUnit_intCast_rat _ (primeProd_ne_zero S)))).obj (structureModule _)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«GlueBundles».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_GlueBundles_hypotheses_inhabited_d52ffbd2fcda

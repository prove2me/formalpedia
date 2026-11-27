-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumCut_proof_5044aa527abb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumCut_proof_5044aa527abb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:28:25.434191+00:00
-- url     : https://prove2.me/theorems/d5b7c173-389b-50a2-b057-7978e09dcb7c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Cut proof 5044aa527abb: P2 M Ground Theory Heights  Heights Kleiman Inter Num Cut proof 5044aa527abb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Cut proof 5044aa527abb construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Cut proof 5044aa527abb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumCut.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumCut.lean#L35-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StCutRestrLenExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutZeroNotLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TensorSubInsertion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumCut
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CutZeroNotLe_proof_5cdce7be14c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ZeroIdealChart_proof_6f00db9dd451
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_KleimanIntersectionNumberCut_proof__9272f1faa9bf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumCut_proof_5044aa527abb (hF : CycleSplit.Filt.Statement.{u, w}) (hA : CutRestrLenExact.Statement.{u, w})
    (hB : MixedTwistShift.Statement.{u, w}) : InterNumCut.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumCut».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumCut_proof_5044aa527abb

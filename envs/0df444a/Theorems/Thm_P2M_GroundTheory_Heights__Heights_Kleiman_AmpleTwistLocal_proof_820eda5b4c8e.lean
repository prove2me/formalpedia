-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_proof_820eda5b4c8e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_proof_820eda5b4c8e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:46.667901+00:00
-- url     : https://prove2.me/theorems/d3908477-4fb0-4b9d-a017-4747bb364c11
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local proof 820eda5b4c8e: P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local proof 820eda5b4c8e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local proof 820eda5b4c8e construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local proof 820eda5b4c8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleTwistLocal.lean#L80-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleTwistLocal.lean#L80-L114

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmpleAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
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
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_proof_820eda5b4c8e (hA : AmpleAffineGen.Statement.{u, w}) : AmpleTwistLocal.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleTwistLocal».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_proof_820eda5b4c8e

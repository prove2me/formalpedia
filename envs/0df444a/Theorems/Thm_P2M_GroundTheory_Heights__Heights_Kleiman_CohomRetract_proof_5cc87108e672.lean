-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CohomRetract_proof_5cc87108e672
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CohomRetract_proof_5cc87108e672
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:55.92856+00:00
-- url     : https://prove2.me/theorems/964cb1de-04e0-466c-83ba-55df64e89a5d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cohom Retract proof 5cc87108e672: P2 M Ground Theory Heights  Heights Kleiman Cohom Retract proof 5cc87108e672
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cohom Retract proof 5cc87108e672 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cohom Retract proof 5cc87108e672 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCohomRetract.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCohomRetract.lean#L36-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCohomRetract
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
universe u v w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CohomRetract_proof_5cc87108e672 : CohomRetract.Statement.{u, v, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CohomRetract».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_CohomRetract_proof_5cc87108e672

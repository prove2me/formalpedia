-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_proof_44434063569b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_proof_44434063569b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:01.071023+00:00
-- url     : https://prove2.me/theorems/7ba8fe25-b248-4134-9bdf-e58c3da585e6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact proof 44434063569b: P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact proof 44434063569b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact proof 44434063569b construction uses the P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact proof 44434063569b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDegLocExact.lean#L69-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDegLocExact.lean#L69-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDegLocExact
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
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.DegLocExact
variable {S : Type u} [CommRing S] {N : ℕ} {M : Type v} [AddCommGroup M] [Module (Poly S N) M]
  [Module S M] [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_proof_44434063569b : DegLocExact.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«DegLocExact».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_proof_44434063569b

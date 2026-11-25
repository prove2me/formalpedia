-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_smul_quot_eq_zero_49b6d7eeda92
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_smul_quot_eq_zero_49b6d7eeda92
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:10.483888+00:00
-- url     : https://prove2.me/theorems/db2188b9-abce-429f-b639-3a42a07c2f23
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman smul quot eq zero 49b6d7eeda92: P2 M Ground Theory Heights  Heights Kleiman smul quot eq zero 49b6d7eeda92
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman smul quot eq zero 49b6d7eeda92 construction uses the P2 M Ground Theory Heights  Heights Kleiman smul quot eq zero 49b6d7eeda92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L77-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_smul_quot_eq_zero_49b6d7eeda92 {q : Poly S N} (hq : q ∈ primeOf (S := S) y)
    (m : Poly S N ⧸ primeOf (S := S) y) : q • m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«smul_quot_eq_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_smul_quot_eq_zero_49b6d7eeda92

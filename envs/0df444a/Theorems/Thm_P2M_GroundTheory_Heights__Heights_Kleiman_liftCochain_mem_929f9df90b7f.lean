-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_mem_929f9df90b7f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_mem_929f9df90b7f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:18:26.25293+00:00
-- url     : https://prove2.me/theorems/3323ce45-bcc3-4145-a6f1-eb286dd65fe5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman lift Cochain mem 929f9df90b7f: P2 M Ground Theory Heights  Heights Kleiman lift Cochain mem 929f9df90b7f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman lift Cochain mem 929f9df90b7f construction uses the P2 M Ground Theory Heights  Heights Kleiman lift Cochain mem 929f9df90b7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L52-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
variable (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_mem_929f9df90b7f {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i) :
    liftCochain M c t ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«liftCochain_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_mem_929f9df90b7f

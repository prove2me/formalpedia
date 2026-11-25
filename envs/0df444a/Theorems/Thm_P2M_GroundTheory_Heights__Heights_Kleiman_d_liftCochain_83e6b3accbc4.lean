-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_d_liftCochain_83e6b3accbc4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_d_liftCochain_83e6b3accbc4
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:37.530633+00:00
-- url     : https://prove2.me/theorems/1e4ad629-aa0d-5e7c-b698-52e40c6b0eb0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman d lift Cochain 83e6b3accbc4: P2 M Ground Theory Heights  Heights Kleiman d lift Cochain 83e6b3accbc4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman d lift Cochain 83e6b3accbc4 construction uses the P2 M Ground Theory Heights  Heights Kleiman d lift Cochain 83e6b3accbc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L73-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L73-L101

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_d_liftCochain_83e6b3accbc4 {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) (i + 1))
    (ht : Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res (i + 1) t = 0) :
    Cech.d (locSys S N M.coneSubE) locResS (i + 1) (liftCochain M c t) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«d_liftCochain» := P2M_GroundTheory_Heights__Heights_Kleiman_d_liftCochain_83e6b3accbc4

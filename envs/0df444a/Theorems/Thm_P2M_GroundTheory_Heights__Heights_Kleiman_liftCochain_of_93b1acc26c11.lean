-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_of_93b1acc26c11
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_of_93b1acc26c11
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:44.428108+00:00
-- url     : https://prove2.me/theorems/d3016319-1982-598b-8b8a-68a785e494fe
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman lift Cochain of 93b1acc26c11: P2 M Ground Theory Heights  Heights Kleiman lift Cochain of 93b1acc26c11
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman lift Cochain of 93b1acc26c11 construction uses the P2 M Ground Theory Heights  Heights Kleiman lift Cochain of 93b1acc26c11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L47-L50

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_of_93b1acc26c11 {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i)
    (J : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) (hJ : J.1.1 ⊆ support x) :
    liftCochain M c t J = liftTilde M c J.1 hJ (t ⟨⟨J.1.1, J.1.2.1, hJ⟩, J.2⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«liftCochain_of» := P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_of_93b1acc26c11

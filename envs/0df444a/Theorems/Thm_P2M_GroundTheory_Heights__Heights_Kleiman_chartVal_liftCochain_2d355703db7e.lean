-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartVal_liftCochain_2d355703db7e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_chartVal_liftCochain_2d355703db7e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:37:27.930906+00:00
-- url     : https://prove2.me/theorems/866d4a0d-96a6-4ecd-9c79-ae94935c57c0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman chart Val lift Cochain 2d355703db7e: P2 M Ground Theory Heights  Heights Kleiman chart Val lift Cochain 2d355703db7e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman chart Val lift Cochain 2d355703db7e construction uses the P2 M Ground Theory Heights  Heights Kleiman chart Val lift Cochain 2d355703db7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFiniteE.lean#L135-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFiniteE.lean#L135-L141

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteESt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFiniteE
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
  (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_chartVal_liftCochain_2d355703db7e {n : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n)
    (I : Cech.Idx (support x) n) : chartVal M c (liftCochain M c t) I = (t I : E) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«chartVal_liftCochain» := P2M_GroundTheory_Heights__Heights_Kleiman_chartVal_liftCochain_2d355703db7e

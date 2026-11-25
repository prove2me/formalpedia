-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_d_a1b4827e5d39
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_d_a1b4827e5d39
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:51.063846+00:00
-- url     : https://prove2.me/theorems/39bc69a1-b158-577b-98db-2de5dc9ac1ff
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Cone E d a1b4827e5d39: P2 M Ground Theory Heights  Heights Kleiman loc Cone E d a1b4827e5d39
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Cone E d a1b4827e5d39 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Cone E d a1b4827e5d39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L62-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L62-L71

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_d_a1b4827e5d39 {i : ℕ} (z : Cech.Cochain (locSys S N M.coneSubE) i)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) (i + 1)) (hK : K.1.1 ⊆ support x) :
    locConeE M K.1.1 hK (Cech.d (locSys S N M.coneSubE) locResS i z K) =
      ∑ j : K.1.1, Cech.sgn K.1.1 j • locConeE M (Cech.face K j).1.1
        ((Cech.face_subset K j).trans hK) (z (Cech.face K j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locConeE_d» := P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_d_a1b4827e5d39

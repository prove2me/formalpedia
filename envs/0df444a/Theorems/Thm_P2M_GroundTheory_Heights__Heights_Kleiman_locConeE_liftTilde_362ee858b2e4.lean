-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_liftTilde_362ee858b2e4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_liftTilde_362ee858b2e4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:54.545328+00:00
-- url     : https://prove2.me/theorems/e092dc8e-7b06-5940-a2b0-ce9accdfc16a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Cone E lift Tilde 362ee858b2e4: P2 M Ground Theory Heights  Heights Kleiman loc Cone E lift Tilde 362ee858b2e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Cone E lift Tilde 362ee858b2e4 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Cone E lift Tilde 362ee858b2e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L39-L41

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_liftTilde_362ee858b2e4 (I : StdCell N) (hI : I.1 ⊆ support x) (y : M.tilde c ⟨I.1, I.2.1, hI⟩) :
    locConeE M I.1 hI (liftTilde M c I hI y) = singleE S x E c y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locConeE_liftTilde» := P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_liftTilde_362ee858b2e4

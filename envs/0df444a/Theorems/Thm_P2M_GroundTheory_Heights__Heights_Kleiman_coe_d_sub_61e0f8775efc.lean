-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coe_d_sub_61e0f8775efc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coe_d_sub_61e0f8775efc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:46.62073+00:00
-- url     : https://prove2.me/theorems/684d1354-bc1b-5818-842e-de8a51b5003b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman coe d sub 61e0f8775efc: P2 M Ground Theory Heights  Heights Kleiman coe d sub 61e0f8775efc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman coe d sub 61e0f8775efc construction uses the P2 M Ground Theory Heights  Heights Kleiman coe d sub 61e0f8775efc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L20-L27

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coe_d_sub_61e0f8775efc (F : SubSystem S x E) {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥(F.sub I)) i)
    (J : Cech.Idx (support x) (i + 1)) :
    ((Cech.d (fun I : Chart x => ↥(F.sub I)) F.res i t J : F.sub J.1) : E) =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • (t (Cech.face J j) : E) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coe_d_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_coe_d_sub_61e0f8775efc

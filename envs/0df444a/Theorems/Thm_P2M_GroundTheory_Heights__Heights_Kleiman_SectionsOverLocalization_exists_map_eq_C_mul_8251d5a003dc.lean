-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_map_eq_C_mul_8251d5a003dc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_map_eq_C_mul_8251d5a003dc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:57:35.684795+00:00
-- url     : https://prove2.me/theorems/b3ccc65b-e4a7-477f-8f4e-580a7964c3a2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists map eq C mul 8251d5a003dc: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists map eq C mul 8251
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists map eq C mul 8251d5a003dc construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists map eq C mul 8251d5a003dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L32-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L32-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
noncomputable section
variable {S : Type*} [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] {O : Type*} [CommRing O] [Algebra S O]
  [IsLocalization.AtPrime O 𝔪] {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
  {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_map_eq_C_mul_8251d5a003dc (f : Poly O N) :
    ∃ t : S, t ∉ 𝔪 ∧ ∃ g : Poly S N, map (algebraMap S O) g = C (algebraMap S O t) * f ∧
      ∀ d, g.coeff d ≠ 0 → f.coeff d ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«exists_map_eq_C_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_map_eq_C_mul_8251d5a003dc

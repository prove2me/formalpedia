-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_RamificationLowerIndex_ramificationIndex_mul_lowerIndex_restrictNormalHom__56df8d42432e
-- name    : P2M_UpperTheory_Reformulated_B_RamificationLowerIndex_ramificationIndex_mul_lowerIndex_restrictNormalHom__56df8d42432e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:05:37.877821+00:00
-- url     : https://prove2.me/theorems/3796e52c-b83c-538e-897a-acbce4566ac6
-- title:
--   P2 M Upper Theory Reformulated B Ramification Lower Index ramification Index mul lower Index restrict Normal Hom  56df8d42432e: P2 M Upper Theory Reformulated B Ramification Lower Index ramification I
-- statement:
--   The P2 M Upper Theory Reformulated B Ramification Lower Index ramification Index mul lower Index restrict Normal Hom  56df8d42432e construction uses the P2 M Upper Theory Reformulated B Ramification Lower Index ramification Index mul lower Index restrict Normal Hom  56df8d42432e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/RamificationLowerIndex.lean#L156-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/RamificationLowerIndex.lean#L156-L229

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RamificationLowerIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open Polynomial IsLocalRing ValuativeRel GroundTheory.LocalField
open IsDiscreteValuationRing hiding maximalIdeal

theorem P2M_UpperTheory_Reformulated_B_RamificationLowerIndex_ramificationIndex_mul_lowerIndex_restrictNormalHom__56df8d42432e.{u_1, u_2} :
    ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [inst_3 : IsNonarchimedeanLocalField K] [inst_4 : Field L] [inst_5 : ValuativeRel L] [inst_6 : TopologicalSpace L]
      [inst_7 : IsNonarchimedeanLocalField L] [inst_8 : Algebra K L] [inst_9 : ValuativeExtension K L]
      [inst_10 : FiniteDimensional K L] (M : IntermediateField K L) [IsGalois K L] [inst_12 : Normal K ↥M] (σ : Gal(L/K)),
      (↑(GroundTheory.LocalField.ramificationIndex (↥M) L) : ℕ∞) *
          GroundTheory.LocalField.lowerIndex K (↥M) ((AlgEquiv.restrictNormalHom ↥M : Gal(L/K) → Gal(↥M/K)) σ) =
        ∑ τ : Gal(L/↥M), GroundTheory.LocalField.lowerIndex K L (σ * AlgEquiv.restrictScalars K τ) := by sorry

alias «UpperTheory».«Reformulated».«B».«RamificationLowerIndex».«ramificationIndex_mul_lowerIndex_restrictNormalHom».«» := P2M_UpperTheory_Reformulated_B_RamificationLowerIndex_ramificationIndex_mul_lowerIndex_restrictNormalHom__56df8d42432e

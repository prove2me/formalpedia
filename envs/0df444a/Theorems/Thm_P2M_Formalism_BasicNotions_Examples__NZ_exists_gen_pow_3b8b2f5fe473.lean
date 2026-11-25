-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_gen_pow_3b8b2f5fe473
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_exists_gen_pow_3b8b2f5fe473
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:25.219333+00:00
-- url     : https://prove2.me/theorems/8a512249-d04a-46a2-a2d2-ad3ec50da230
-- title:
--   P2 M Formalism Basic Notions Examples  NZ exists gen pow 3b8b2f5fe473: P2 M Formalism Basic Notions Examples  NZ exists gen pow 3b8b2f5fe473
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ exists gen pow 3b8b2f5fe473 construction uses the P2 M Formalism Basic Notions Examples  NZ exists gen pow 3b8b2f5fe473 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevA.lean#L35-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevA.lean#L35-L72

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZLevA
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Formalism.MainNotions.G
variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q] [Algebra W Q] [IsFractionRing W Q]
  (ϖ : W) (hϖ : Irreducible ϖ)
local notation "π" => algebraMap W Q ϖ
include hϖ

theorem P2M_Formalism_BasicNotions_Examples__NZ_exists_gen_pow_3b8b2f5fe473 (I : Submodule W Q) (h0 : ∃ x ∈ I, x ≠ 0) (N : ℕ)
    (hN : ∀ x ∈ I, π ^ N * x ∈ (algebraMap W Q).range) :
    ∃ n : ℤ, π ^ n ∈ I ∧ ∀ x ∈ I, ∃ a : W, x = algebraMap W Q a * π ^ n := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«exists_gen_pow» := P2M_Formalism_BasicNotions_Examples__NZ_exists_gen_pow_3b8b2f5fe473

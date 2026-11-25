-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_den_6be64aadeaa6
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_exists_den_6be64aadeaa6
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:00.131904+00:00
-- url     : https://prove2.me/theorems/a8194ef2-f5d6-4621-a2bc-9d21b9eef39a
-- title:
--   P2 M Formalism Basic Notions Examples  NZ exists den 6be64aadeaa6: P2 M Formalism Basic Notions Examples  NZ exists den 6be64aadeaa6
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ exists den 6be64aadeaa6 construction uses the P2 M Formalism Basic Notions Examples  NZ exists den 6be64aadeaa6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevA.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevA.lean#L18-L29

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_exists_den_6be64aadeaa6 (q : Q) : ∃ N : ℕ, ∀ M, N ≤ M → π ^ M * q ∈ (algebraMap W Q).range := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«exists_den» := P2M_Formalism_BasicNotions_Examples__NZ_exists_den_6be64aadeaa6

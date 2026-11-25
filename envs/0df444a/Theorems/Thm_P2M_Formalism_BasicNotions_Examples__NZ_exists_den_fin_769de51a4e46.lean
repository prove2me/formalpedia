-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_den_fin_769de51a4e46
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_exists_den_fin_769de51a4e46
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:00.031438+00:00
-- url     : https://prove2.me/theorems/29344ab5-8e44-43ce-b745-2d2514220adb
-- title:
--   P2 M Formalism Basic Notions Examples  NZ exists den fin 769de51a4e46: P2 M Formalism Basic Notions Examples  NZ exists den fin 769de51a4e46
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ exists den fin 769de51a4e46 construction uses the P2 M Formalism Basic Notions Examples  NZ exists den fin 769de51a4e46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevA.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevA.lean#L31-L33

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_exists_den_fin_769de51a4e46 {ι : Type} [Fintype ι] (q : ι → Q) : ∃ N : ℕ, ∀ i, π ^ N * q i ∈ (algebraMap W Q).range := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«exists_den_fin» := P2M_Formalism_BasicNotions_Examples__NZ_exists_den_fin_769de51a4e46

-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_pi_ne_da2d4218d599
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_pi_ne_da2d4218d599
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:26.759994+00:00
-- url     : https://prove2.me/theorems/44358069-b954-45e1-9ea2-b62e28e061c1
-- title:
--   P2 M Formalism Basic Notions Examples  NZ pi ne da2d4218d599: P2 M Formalism Basic Notions Examples  NZ pi ne da2d4218d599
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ pi ne da2d4218d599 construction uses the P2 M Formalism Basic Notions Examples  NZ pi ne da2d4218d599 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevA.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevA.lean#L16-L16

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_pi_ne_da2d4218d599 : π ≠ 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«pi_ne» := P2M_Formalism_BasicNotions_Examples__NZ_pi_ne_da2d4218d599

-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_hermite_032dc7ca396f
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_hermite_032dc7ca396f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:07.525467+00:00
-- url     : https://prove2.me/theorems/77fbd4a6-139d-4086-9f43-949e89286a97
-- title:
--   P2 M Formalism Basic Notions Examples  NZ hermite 032dc7ca396f: P2 M Formalism Basic Notions Examples  NZ hermite 032dc7ca396f
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ hermite 032dc7ca396f construction uses the P2 M Formalism Basic Notions Examples  NZ hermite 032dc7ca396f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevA.lean#L86-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevA.lean#L86-L170

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
variable {k : ℕ}

theorem P2M_Formalism_BasicNotions_Examples__NZ_hermite_032dc7ca396f (L : Submodule W (Fin k → Q)) (hL : IsLattice W L) :
    ∃ (A : Matrix (Fin k) (Fin k) Q) (n : Fin k → ℤ), (∀ i j, i < j → A i j = 0) ∧ (∀ a, A a a = π ^ n a) ∧
      L = colSpan W A := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«hermite» := P2M_Formalism_BasicNotions_Examples__NZ_hermite_032dc7ca396f

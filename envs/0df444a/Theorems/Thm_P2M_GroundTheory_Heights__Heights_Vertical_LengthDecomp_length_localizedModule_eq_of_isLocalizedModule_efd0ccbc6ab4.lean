-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_eq_of_isLocalizedModule_efd0ccbc6ab4
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_eq_of_isLocalizedModule_efd0ccbc6ab4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:17.838123+00:00
-- url     : https://prove2.me/theorems/4feb4e3d-34e0-437e-970b-59f3c33a4591
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Length Decomp length localized Module eq of is Localized Module efd0ccbc6ab4: P2 M Ground Theory Heights  Heights Vertical Length Decomp length localized M
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Length Decomp length localized Module eq of is Localized Module efd0ccbc6ab4 construction uses the P2 M Ground Theory Heights  Heights Vertical Length Decomp length localized Module eq of is Localized Module efd0ccbc6ab4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PLengthDecomp.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PLengthDecomp.lean#L17-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open Module IsLocalRing LinearMap Submodule
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
open Classical
variable {B : Type*} [CommRing B]

theorem P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_eq_of_isLocalizedModule_efd0ccbc6ab4 (p : Ideal B) [p.IsPrime]
    {X Y : Type*} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y]
    [Module (Localization.AtPrime p) Y] [IsScalarTower B (Localization.AtPrime p) Y]
    (g : X →ₗ[B] Y) [IsLocalizedModule p.primeCompl g] :
    length (Localization.AtPrime p) (LocalizedModule p.primeCompl X) =
      length (Localization.AtPrime p) Y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«LengthDecomp».«length_localizedModule_eq_of_isLocalizedModule» := P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_eq_of_isLocalizedModule_efd0ccbc6ab4

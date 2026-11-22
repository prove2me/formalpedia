-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__placesOf_val_eq_3e0aa8fce33c
-- name    : P2M_Formalism_BasicNotions_Examples__placesOf_val_eq_3e0aa8fce33c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:26:34.701654+00:00
-- url     : https://prove2.me/theorems/3b091e73-460f-4ce1-abc4-a590a6494fef
-- title:
--   P2 M Formalism Basic Notions Examples  places Of val eq 3e0aa8fce33c: P2 M Formalism Basic Notions Examples  places Of val eq 3e0aa8fce33c
-- statement:
--   The P2 M Formalism Basic Notions Examples  places Of val eq 3e0aa8fce33c construction uses the P2 M Formalism Basic Notions Examples  places Of val eq 3e0aa8fce33c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L320-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L320-L323

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
variable (K : Type) [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_BasicNotions_Examples__placesOf_val_eq_3e0aa8fce33c (w : (placesOf K).Pl) (x : K) (hx : x ≠ 0) :
    (placesOf K).val w x = ((vAdd ((Equiv.refl _ : (placesOf K).Pl ≃ HeightOneSpectrum (𝓞 K)) w) x : ℤ) :
      WithTop ℤ) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«placesOf_val_eq» := P2M_Formalism_BasicNotions_Examples__placesOf_val_eq_3e0aa8fce33c

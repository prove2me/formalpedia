-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CentredRingNormal_absCentredAt_of_le_one_ebd98841079e
-- name    : P2M_GroundTheory_Heights__Heights_CentredRingNormal_absCentredAt_of_le_one_ebd98841079e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:26.585224+00:00
-- url     : https://prove2.me/theorems/7e96cb09-43e8-4e54-861e-ee3f4d529327
-- title:
--   P2 M Ground Theory Heights  Heights Centred Ring Normal abs Centred At of le one ebd98841079e: P2 M Ground Theory Heights  Heights Centred Ring Normal abs Centred At of le one ebd98841079e
-- statement:
--   The P2 M Ground Theory Heights  Heights Centred Ring Normal abs Centred At of le one ebd98841079e construction uses the P2 M Ground Theory Heights  Heights Centred Ring Normal abs Centred At of le one ebd98841079e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PCentredRingNormal.lean#L68-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PCentredRingNormal.lean#L68-L116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredRingNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PCentredRingNormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField IsDedekindDomain
open GroundTheory.Heights₂.Heights.CentredRingNormal
variable {L : Type} [Field L] [NumberField L]

theorem P2M_GroundTheory_Heights__Heights_CentredRingNormal_absCentredAt_of_le_one_ebd98841079e (O : Subalgebra ℤ L) [IsFractionRing O L] (m : Ideal O) [m.IsMaximal]
    (w : FinitePlace L)
    (hA : ∀ y ∈ Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors,
      w y ≤ 1)
    (x : L) (hx : 1 < w x) : AbsCentredAt O m fun t ↦ w t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CentredRingNormal».«absCentredAt_of_le_one» := P2M_GroundTheory_Heights__Heights_CentredRingNormal_absCentredAt_of_le_one_ebd98841079e

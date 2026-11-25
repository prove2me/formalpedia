-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_subsingleton_of_not_le_8af77c4e3823
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_subsingleton_of_not_le_8af77c4e3823
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:03.243121+00:00
-- url     : https://prove2.me/theorems/745a4e4d-6631-5300-8cef-5fe1297015c4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR localized Quotient subsingleton of not le 8af77c4e3823: P2 M Ground Theory Heights  Heights Numbers DVR localized Quotient subsingleton of not le 8af77c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR localized Quotient subsingleton of not le 8af77c4e3823 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR localized Quotient subsingleton of not le 8af77c4e3823 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultAtPrimeAtMinimal.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultAtPrimeAtMinimal.lean#L11-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultAtPrimeAtMinimal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
variable {A : Type*} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_subsingleton_of_not_le_8af77c4e3823 (Q W : Ideal A) [W.IsPrime] (h : ¬ Q ≤ W) :
    Subsingleton (LocalizedModule W.primeCompl (A ⧸ Q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«localizedQuotient_subsingleton_of_not_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_subsingleton_of_not_le_8af77c4e3823

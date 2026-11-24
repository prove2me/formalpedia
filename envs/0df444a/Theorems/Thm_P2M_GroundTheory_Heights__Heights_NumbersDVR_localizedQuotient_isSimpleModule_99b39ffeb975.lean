-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_isSimpleModule_99b39ffeb975
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_isSimpleModule_99b39ffeb975
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:36.524783+00:00
-- url     : https://prove2.me/theorems/783f6892-cdaf-4300-81b6-2a62b11a39ee
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR localized Quotient is Simple Module 99b39ffeb975: P2 M Ground Theory Heights  Heights Numbers DVR localized Quotient is Simple Module 99b39ffeb975
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR localized Quotient is Simple Module 99b39ffeb975 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR localized Quotient is Simple Module 99b39ffeb975 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultAtPrimeAtMinimal.lean#L29-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultAtPrimeAtMinimal.lean#L29-L47

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_isSimpleModule_99b39ffeb975 (W : Ideal A) [W.IsPrime] :
    IsSimpleModule (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ W)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«localizedQuotient_isSimpleModule» := P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_isSimpleModule_99b39ffeb975

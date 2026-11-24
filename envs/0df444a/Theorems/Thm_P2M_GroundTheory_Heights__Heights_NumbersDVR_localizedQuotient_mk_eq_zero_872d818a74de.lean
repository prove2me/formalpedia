-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_mk_eq_zero_872d818a74de
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_mk_eq_zero_872d818a74de
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:06.792933+00:00
-- url     : https://prove2.me/theorems/4a653701-8c7b-48f0-b5e4-3b0ed6b1f697
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR localized Quotient mk eq zero 872d818a74de: P2 M Ground Theory Heights  Heights Numbers DVR localized Quotient mk eq zero 872d818a74de
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR localized Quotient mk eq zero 872d818a74de construction uses the P2 M Ground Theory Heights  Heights Numbers DVR localized Quotient mk eq zero 872d818a74de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultAtPrimeAtMinimal.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultAtPrimeAtMinimal.lean#L21-L27

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_mk_eq_zero_872d818a74de (W : Ideal A) [W.IsPrime] (a : A) (s : W.primeCompl)
    (h : LocalizedModule.mk (Ideal.Quotient.mk W a) s = 0) : a ∈ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«localizedQuotient_mk_eq_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_mk_eq_zero_872d818a74de

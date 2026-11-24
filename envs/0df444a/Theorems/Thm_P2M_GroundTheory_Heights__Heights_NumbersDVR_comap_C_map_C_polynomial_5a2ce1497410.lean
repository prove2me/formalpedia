-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_map_C_polynomial_5a2ce1497410
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_map_C_polynomial_5a2ce1497410
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:17.117777+00:00
-- url     : https://prove2.me/theorems/73efe6cf-fbcd-4325-bdfd-6e24c6cefe2f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR comap C map C polynomial 5a2ce1497410: P2 M Ground Theory Heights  Heights Numbers DVR comap C map C polynomial 5a2ce1497410
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR comap C map C polynomial 5a2ce1497410 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR comap C map C polynomial 5a2ce1497410 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPolynomialLocalizedLength.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPolynomialLocalizedLength.lean#L26-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontalMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
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
open IsLocalRing
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_map_C_polynomial_5a2ce1497410 {R : Type*} [CommRing R] (p : Ideal R) :
    (p.map (Polynomial.C : R →+* Polynomial R)).comap (Polynomial.C : R →+* Polynomial R) = p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«comap_C_map_C_polynomial» := P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_map_C_polynomial_5a2ce1497410

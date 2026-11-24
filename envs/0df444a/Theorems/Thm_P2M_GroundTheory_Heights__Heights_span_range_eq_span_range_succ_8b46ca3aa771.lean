-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_span_range_eq_span_range_succ_8b46ca3aa771
-- name    : P2M_GroundTheory_Heights__Heights_span_range_eq_span_range_succ_8b46ca3aa771
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:38.643992+00:00
-- url     : https://prove2.me/theorems/c3d74990-ca7d-4fa4-9fcb-10e034abb824
-- title:
--   P2 M Ground Theory Heights  Heights span range eq span range succ 8b46ca3aa771: P2 M Ground Theory Heights  Heights span range eq span range succ 8b46ca3aa771
-- statement:
--   The P2 M Ground Theory Heights  Heights span range eq span range succ 8b46ca3aa771 construction uses the P2 M Ground Theory Heights  Heights span range eq span range succ 8b46ca3aa771 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMLengthParameters.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMLengthParameters.lean#L54-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMLengthParameters
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
open IsLocalRing
universe u

theorem P2M_GroundTheory_Heights__Heights_span_range_eq_span_range_succ_8b46ca3aa771 {R : Type*} [CommRing R] {k : ℕ} (z : Fin (k + 1) → R) (h0 : z 0 = 0) :
    Ideal.span (Set.range z) = Ideal.span (Set.range fun j : Fin k => z j.succ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«span_range_eq_span_range_succ» := P2M_GroundTheory_Heights__Heights_span_range_eq_span_range_succ_8b46ca3aa771

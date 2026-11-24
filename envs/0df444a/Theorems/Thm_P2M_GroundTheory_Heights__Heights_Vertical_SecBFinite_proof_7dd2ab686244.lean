-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_proof_7dd2ab686244
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_proof_7dd2ab686244
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:08.512952+00:00
-- url     : https://prove2.me/theorems/c85688f7-20cd-4b4e-b347-c50e74799946
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite proof 7dd2ab686244: P2 M Ground Theory Heights  Heights Vertical Sec BFinite proof 7dd2ab686244
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite proof 7dd2ab686244 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite proof 7dd2ab686244 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L267-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L267-L353

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
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
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
open SecBFinite

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_proof_7dd2ab686244 (hIN : IncidenceNull.Statement) (hCT : ChartTorsion.Statement)
    (hPS : PrimitiveScale.Statement) : SecBFinite.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«proof» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_proof_7dd2ab686244

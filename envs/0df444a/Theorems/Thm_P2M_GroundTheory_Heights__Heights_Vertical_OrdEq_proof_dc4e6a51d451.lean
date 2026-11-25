-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_OrdEq_proof_dc4e6a51d451
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_OrdEq_proof_dc4e6a51d451
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:08.182988+00:00
-- url     : https://prove2.me/theorems/5f0a7720-643f-4211-9450-b28975911d6a
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Ord Eq proof dc4e6a51d451: P2 M Ground Theory Heights  Heights Vertical Ord Eq proof dc4e6a51d451
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Ord Eq proof dc4e6a51d451 construction uses the P2 M Ground Theory Heights  Heights Vertical Ord Eq proof dc4e6a51d451 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/POrdEq.lean#L22-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/POrdEq.lean#L22-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_POrdEq
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
open Classical

theorem P2M_GroundTheory_Heights__Heights_Vertical_OrdEq_proof_dc4e6a51d451 (hni : NormIdentity.Statement) (hnl : NormLength.Statement)
    (hld : LengthDecomp.Statement) (hmax : SpecMax.Statement) (hlen : SpecLength.Statement)
    (hres : SpecResidue.Statement) (hvs : VertSpec.Statement) (hinj : SecBLinInj.Statement)
    (hfin : SecBFinite.Statement) (htf : SecBTorsionFree.Statement) (hdvr : ParDVRIsDVR.Statement) :
    OrdEq.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«OrdEq».«proof» := P2M_GroundTheory_Heights__Heights_Vertical_OrdEq_proof_dc4e6a51d451

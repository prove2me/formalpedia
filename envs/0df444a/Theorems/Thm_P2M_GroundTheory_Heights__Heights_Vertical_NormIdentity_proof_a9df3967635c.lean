-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormIdentity_proof_a9df3967635c
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormIdentity_proof_a9df3967635c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:14.351873+00:00
-- url     : https://prove2.me/theorems/be6f437a-557f-404e-8647-5cb52cc99189
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Identity proof a9df3967635c: P2 M Ground Theory Heights  Heights Vertical Norm Identity proof a9df3967635c
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Identity proof a9df3967635c construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Identity proof a9df3967635c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L79-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L79-L155

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormIdentity
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

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormIdentity_proof_a9df3967635c (hcn : ChowNormForm.Statement) (hfin : SecBFinite.Statement)
    (htf : SecBTorsionFree.Statement) (hgen : SecBGeneric.Statement)
    (hloc : NormFormLocalization.Statement) (hev : NormFormEval.Statement)
    (hai : ParAlgIndep.Statement) (hfr : ParFracIsFractionRing.Statement)
    (hdvr : ParDVRIsDVR.Statement) : NormIdentity.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormIdentity».«proof» := P2M_GroundTheory_Heights__Heights_Vertical_NormIdentity_proof_a9df3967635c

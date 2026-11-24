-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecResidue_proof_62605cd37d88
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecResidue_proof_62605cd37d88
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:25.776848+00:00
-- url     : https://prove2.me/theorems/da62b4cc-2919-469b-8882-b7351c07fb60
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Residue proof 62605cd37d88: P2 M Ground Theory Heights  Heights Vertical Spec Residue proof 62605cd37d88
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Residue proof 62605cd37d88 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Residue proof 62605cd37d88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecResidue.lean#L12-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecResidue.lean#L12-L98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecResidue
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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecResidue_proof_62605cd37d88 (hCSD : ChowSecDegree.Statement) (hCNF : ChowNormForm.Statement)
    (hDim : SpecCompDim.Statement) (hExist : ChowFormExists.Statement)
    (hInd : ResidueAlgIndep.Statement) : SpecResidue.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecResidue».«proof» := P2M_GroundTheory_Heights__Heights_Vertical_SpecResidue_proof_62605cd37d88

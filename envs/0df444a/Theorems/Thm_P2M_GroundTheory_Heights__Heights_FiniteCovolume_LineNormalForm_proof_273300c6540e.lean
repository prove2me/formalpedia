-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_proof_273300c6540e
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_proof_273300c6540e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:14:37.207116+00:00
-- url     : https://prove2.me/theorems/af7a5844-eb3e-5f14-990e-cc4eaadb158d
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form proof 273300c6540e: P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form proof 273300c6540e
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form proof 273300c6540e construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form proof 273300c6540e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L90-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L90-L305

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIdealClassesFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineCoeffsFG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsCommonMultiple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineNormalForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IdealClassesFinite_proof_91676186b289
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineCoeffsFG_proof_53ed2500803f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LinePairOrbitsFinite_proof_09504d4235de

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
open LineNormalForm
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_proof_273300c6540e (h : HermitianForm F E W) : LineNormalForm.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«LineNormalForm».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_proof_273300c6540e

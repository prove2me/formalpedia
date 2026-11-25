-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_proof_758aa28dabbc
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_proof_758aa28dabbc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:14:15.715648+00:00
-- url     : https://prove2.me/theorems/c3727492-cafc-5796-959f-fb4edf02ea78
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent proof 758aa28dabbc: P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent proof 758aa28dabbc
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent proof 758aa28dabbc construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent proof 758aa28dabbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRationalUnipotent.lean#L107-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRationalUnipotent.lean#L107-L141

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRationalUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open RationalUnipotent

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_proof_758aa28dabbc (h : HermitianForm F E W) : RationalUnipotent.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«RationalUnipotent».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_proof_758aa28dabbc

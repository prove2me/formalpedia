-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_hermPair_comm_dfd82cefa166
-- name    : P2M_GroundTheory_Heights__Theta_hermPair_comm_dfd82cefa166
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:53:48.584982+00:00
-- url     : https://prove2.me/theorems/12578dca-b9de-5005-985f-f218d7d5b4b2
-- title:
--   P2 M Ground Theory Heights  Theta herm Pair comm dfd82cefa166: P2 M Ground Theory Heights  Theta herm Pair comm dfd82cefa166
-- statement:
--   The P2 M Ground Theory Heights  Theta herm Pair comm dfd82cefa166 construction uses the P2 M Ground Theory Heights  Theta herm Pair comm dfd82cefa166 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L54-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L54-L64

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Module Matrix TensorProduct GroundTheory.Automorphic NumberField
open scoped NumberField.AdeleRing
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical
variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K) (H : Matrix ι ι E)
variable {K H}

theorem P2M_GroundTheory_Heights__Theta_hermPair_comm_dfd82cefa166 (hH : IsHermitianFor (conjHom K E) H) (x y : ι → E) :
    hermPair K H y x = conj K E (hermPair K H x y) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«hermPair_comm» := P2M_GroundTheory_Heights__Theta_hermPair_comm_dfd82cefa166

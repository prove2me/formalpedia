-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_comp_collapse_49ec2e4b76fe
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_comp_collapse_49ec2e4b76fe
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:08.123274+00:00
-- url     : https://prove2.me/theorems/c940dca9-5365-4531-86a9-ef48c2c40603
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible comp collapse 49ec2e4b76fe: P2 M Ground Theory Heights  Heights Antisym Divisible comp collapse 49ec2e4b76fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible comp collapse 49ec2e4b76fe construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible comp collapse 49ec2e4b76fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L19-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {σ : Type*} [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_comp_collapse_49ec2e4b76fe {u v : σ} (x : σ → ℝ) (hx : x u = x v) : x ∘ collapse u v = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«comp_collapse» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_comp_collapse_49ec2e4b76fe

-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_hyps_bc69208ec540
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twist_hyps_bc69208ec540
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:09.534805+00:00
-- url     : https://prove2.me/theorems/ac13ff29-7a83-4d5a-94ed-054f2ddb7fcc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist hyps bc69208ec540: P2 M Ground Theory Heights  Heights Kleiman twist hyps bc69208ec540
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist hyps bc69208ec540 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist hyps bc69208ec540 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Statements.lean#L167-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Statements.lean#L167-L170

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial TensorProduct
noncomputable section
universe u v w
variable (k : Type u) [Field k] (N : ℕ)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twist_hyps_bc69208ec540 {Ω : Type w} [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω) :
    (∀ j, x j ∈ (twistBundle k x 1).secs) ∧
    ∀ I, Submodule.span (chartRing k x I) (Set.range x) = (twistBundle k x 1).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twist_hyps» := P2M_GroundTheory_Heights__Heights_Kleiman_twist_hyps_bc69208ec540

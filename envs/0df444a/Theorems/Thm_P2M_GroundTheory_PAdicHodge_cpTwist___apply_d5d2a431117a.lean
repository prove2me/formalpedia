-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_cpTwist___apply_d5d2a431117a
-- name    : P2M_GroundTheory_PAdicHodge_cpTwist___apply_d5d2a431117a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:35.998269+00:00
-- url     : https://prove2.me/theorems/7d8d5342-4bca-594f-b42d-a55af4351e69
-- title:
--   P2 M Ground Theory PAdic Hodge cp Twist   apply d5d2a431117a: P2 M Ground Theory PAdic Hodge cp Twist   apply d5d2a431117a
-- statement:
--   The P2 M Ground Theory PAdic Hodge cp Twist   apply d5d2a431117a construction uses the P2 M Ground Theory PAdic Hodge cp Twist   apply d5d2a431117a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateCpTwist.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateCpTwist.lean#L99-L100

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open UniformSpace
variable {p : ℕ} [Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem P2M_GroundTheory_PAdicHodge_cpTwist___apply_d5d2a431117a (j : ℤ) (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    (cpTwist K j).ρ σ x = twistScalar K j σ * (σ • x) := by sorry

alias «GroundTheory».«PAdicHodge».«cpTwist_ρ_apply» := P2M_GroundTheory_PAdicHodge_cpTwist___apply_d5d2a431117a

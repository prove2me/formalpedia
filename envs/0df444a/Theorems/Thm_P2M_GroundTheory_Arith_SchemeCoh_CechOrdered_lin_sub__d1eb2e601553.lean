-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_CechOrdered_lin_sub__d1eb2e601553
-- name    : P2M_GroundTheory_Arith_SchemeCoh_CechOrdered_lin_sub__d1eb2e601553
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:38.190217+00:00
-- url     : https://prove2.me/theorems/3cb432e3-8b46-4acd-abd4-2938700b08dd
-- title:
--   P2 M Ground Theory Arith Scheme Coh Cech Ordered lin sub  d1eb2e601553: P2 M Ground Theory Arith Scheme Coh Cech Ordered lin sub  d1eb2e601553
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh Cech Ordered lin sub  d1eb2e601553 construction uses the P2 M Ground Theory Arith Scheme Coh Cech Ordered lin sub  d1eb2e601553 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L183-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L183-L188

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u
open GroundTheory.Arith.SchemeCoh.CechOrdered
variable (ι : Type w)
variable {ι}
variable {q r s : ℕ}

theorem P2M_GroundTheory_Arith_SchemeCoh_CechOrdered_lin_sub__d1eb2e601553 (B B' : (Fin (q + 1) → ι) → Chain ι r) (z : Chain ι q) :
    lin (fun t => B t - B' t) z = lin B z - lin B' z := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«CechOrdered».«lin_sub'» := P2M_GroundTheory_Arith_SchemeCoh_CechOrdered_lin_sub__d1eb2e601553

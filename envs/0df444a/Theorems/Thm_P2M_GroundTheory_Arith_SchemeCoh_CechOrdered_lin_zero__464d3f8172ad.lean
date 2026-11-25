-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_CechOrdered_lin_zero__464d3f8172ad
-- name    : P2M_GroundTheory_Arith_SchemeCoh_CechOrdered_lin_zero__464d3f8172ad
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:12.008137+00:00
-- url     : https://prove2.me/theorems/92ea9d80-82c1-4d7a-a001-873364484f6f
-- title:
--   P2 M Ground Theory Arith Scheme Coh Cech Ordered lin zero  464d3f8172ad: P2 M Ground Theory Arith Scheme Coh Cech Ordered lin zero  464d3f8172ad
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh Cech Ordered lin zero  464d3f8172ad construction uses the P2 M Ground Theory Arith Scheme Coh Cech Ordered lin zero  464d3f8172ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L190-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L190-L194

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

theorem P2M_GroundTheory_Arith_SchemeCoh_CechOrdered_lin_zero__464d3f8172ad (z : Chain ι q) : lin (fun _ => (0 : Chain ι r)) z = 0 := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«CechOrdered».«lin_zero'» := P2M_GroundTheory_Arith_SchemeCoh_CechOrdered_lin_zero__464d3f8172ad

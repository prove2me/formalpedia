-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_isIso_opens___restrict_83dfe4b2a8ea
-- name    : P2M_GroundTheory_Arith_SchemeCoh_isIso_opens___restrict_83dfe4b2a8ea
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:40.976047+00:00
-- url     : https://prove2.me/theorems/47e980de-7e58-4439-b789-db5b65db28c1
-- title:
--   P2 M Ground Theory Arith Scheme Coh is Iso opens   restrict 83dfe4b2a8ea: P2 M Ground Theory Arith Scheme Coh is Iso opens   restrict 83dfe4b2a8ea
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh is Iso opens   restrict 83dfe4b2a8ea construction uses the P2 M Ground Theory Arith Scheme Coh is Iso opens   restrict 83dfe4b2a8ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/IrreducibleImage.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/IrreducibleImage.lean#L13-L21

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SchemeImage
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_IrreducibleImage
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
universe u
noncomputable section

theorem P2M_GroundTheory_Arith_SchemeCoh_isIso_opens___restrict_83dfe4b2a8ea {Z : Scheme.{u}} (O : Z.Opens) : IsIso (O.ι ∣_ O) := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«isIso_opens_ι_restrict» := P2M_GroundTheory_Arith_SchemeCoh_isIso_opens___restrict_83dfe4b2a8ea

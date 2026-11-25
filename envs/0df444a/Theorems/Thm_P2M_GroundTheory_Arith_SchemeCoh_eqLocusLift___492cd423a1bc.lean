-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_eqLocusLift___492cd423a1bc
-- name    : P2M_GroundTheory_Arith_SchemeCoh_eqLocusLift___492cd423a1bc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:28.536136+00:00
-- url     : https://prove2.me/theorems/c0816bbd-915f-5b57-b029-362376430a99
-- title:
--   P2 M Ground Theory Arith Scheme Coh eq Locus Lift   492cd423a1bc: P2 M Ground Theory Arith Scheme Coh eq Locus Lift   492cd423a1bc
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh eq Locus Lift   492cd423a1bc construction uses the P2 M Ground Theory Arith Scheme Coh eq Locus Lift   492cd423a1bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SchemeImage.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SchemeImage.lean#L94-L96

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SchemeImage
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
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
variable {T S B : Scheme.{u}} (p : S ⟶ B) [IsSeparated p] (g h : T ⟶ S) (hgh : g ≫ p = h ≫ p)
omit [IsSeparated p]

theorem P2M_GroundTheory_Arith_SchemeCoh_eqLocusLift___492cd423a1bc {V : Scheme.{u}} (t : V ⟶ T) (ht : t ≫ g = t ≫ h) :
    eqLocusLift p g h hgh t ht ≫ eqLocusι p g h hgh = t := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«eqLocusLift_ι» := P2M_GroundTheory_Arith_SchemeCoh_eqLocusLift___492cd423a1bc

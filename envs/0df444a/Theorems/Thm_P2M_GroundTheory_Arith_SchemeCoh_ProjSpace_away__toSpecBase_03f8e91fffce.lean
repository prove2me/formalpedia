-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_ProjSpace_away__toSpecBase_03f8e91fffce
-- name    : P2M_GroundTheory_Arith_SchemeCoh_ProjSpace_away__toSpecBase_03f8e91fffce
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:35:21.509561+00:00
-- url     : https://prove2.me/theorems/8bea78ba-baf8-5295-83df-cb09155b9b49
-- title:
--   P2 M Ground Theory Arith Scheme Coh Proj Space away  to Spec Base 03f8e91fffce: P2 M Ground Theory Arith Scheme Coh Proj Space away  to Spec Base 03f8e91fffce
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh Proj Space away  to Spec Base 03f8e91fffce construction uses the P2 M Ground Theory Arith Scheme Coh Proj Space away  to Spec Base 03f8e91fffce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L152-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L152-L157

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveSpaceChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjBaseChange
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
open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
variable {A B n}
variable (A)

theorem P2M_GroundTheory_Arith_SchemeCoh_ProjSpace_away__toSpecBase_03f8e91fffce {s : MvPolynomial (Fin (n + 1)) A} {d : ℕ} (hs : s ∈ grading A n d)
    (hd : 0 < d) :
    Proj.awayι (grading A n) s hs hd ≫ toSpecBase A n =
      Spec.map (CommRingCat.ofHom (chartAlgebraMap A s)) := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«ProjSpace».«awayι_toSpecBase» := P2M_GroundTheory_Arith_SchemeCoh_ProjSpace_away__toSpecBase_03f8e91fffce

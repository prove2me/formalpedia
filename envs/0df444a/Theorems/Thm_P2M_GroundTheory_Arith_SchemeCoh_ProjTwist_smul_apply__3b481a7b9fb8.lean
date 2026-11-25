-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_ProjTwist_smul_apply__3b481a7b9fb8
-- name    : P2M_GroundTheory_Arith_SchemeCoh_ProjTwist_smul_apply__3b481a7b9fb8
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:37.71533+00:00
-- url     : https://prove2.me/theorems/0e8189ba-d85f-4281-a228-4e9b71b33dff
-- title:
--   P2 M Ground Theory Arith Scheme Coh Proj Twist smul apply  3b481a7b9fb8: P2 M Ground Theory Arith Scheme Coh Proj Twist smul apply  3b481a7b9fb8
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh Proj Twist smul apply  3b481a7b9fb8 construction uses the P2 M Ground Theory Arith Scheme Coh Proj Twist smul apply  3b481a7b9fb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwist.lean#L133-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwist.lean#L133-L134

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist
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
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
open GroundTheory.Arith.SchemeCoh.ProjTwist
variable {𝒜}
open ProjectiveSpectrum

theorem P2M_GroundTheory_Arith_SchemeCoh_ProjTwist_smul_apply__3b481a7b9fb8 {U : Opens (ProjectiveSpectrum.top 𝒜)} (t : (Proj.structureSheaf 𝒜).obj.obj (op U))
    (f : ∀ x : U, Loc 𝒜 x.1) (x : U) : (t • f) x = (t.1 x).val * f x := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«ProjTwist».«smul_apply'» := P2M_GroundTheory_Arith_SchemeCoh_ProjTwist_smul_apply__3b481a7b9fb8

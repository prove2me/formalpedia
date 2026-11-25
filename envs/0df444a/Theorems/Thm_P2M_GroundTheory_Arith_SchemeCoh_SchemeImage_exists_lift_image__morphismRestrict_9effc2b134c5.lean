-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_SchemeImage_exists_lift_image__morphismRestrict_9effc2b134c5
-- name    : P2M_GroundTheory_Arith_SchemeCoh_SchemeImage_exists_lift_image__morphismRestrict_9effc2b134c5
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:54.087651+00:00
-- url     : https://prove2.me/theorems/38fd1d48-1a37-4719-a4a3-f716b1388119
-- title:
--   P2 M Ground Theory Arith Scheme Coh Scheme Image exists lift image  morphism Restrict 9effc2b134c5: P2 M Ground Theory Arith Scheme Coh Scheme Image exists lift image  morphism Restrict 9effc2b134c5
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh Scheme Image exists lift image  morphism Restrict 9effc2b134c5 construction uses the P2 M Ground Theory Arith Scheme Coh Scheme Image exists lift image  morphism Restrict 9effc2b134c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SchemeImage.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SchemeImage.lean#L22-L28

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
open GroundTheory.Arith.SchemeCoh.SchemeImage
variable {Y Z : Scheme.{u}} (f : Y ⟶ Z) [QuasiCompact f] (W : Z.Opens)

theorem P2M_GroundTheory_Arith_SchemeCoh_SchemeImage_exists_lift_image__morphismRestrict_9effc2b134c5 {C : Scheme.{u}} (c : C ⟶ W.toScheme)
    [IsClosedImmersion c] (g : (f ⁻¹ᵁ W).toScheme ⟶ C) (hg : g ≫ c = f ∣_ W) :
    ∃ k : (f.imageι ⁻¹ᵁ W).toScheme ⟶ C, k ≫ c = f.imageι ∣_ W := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«SchemeImage».«exists_lift_imageι_morphismRestrict» := P2M_GroundTheory_Arith_SchemeCoh_SchemeImage_exists_lift_image__morphismRestrict_9effc2b134c5

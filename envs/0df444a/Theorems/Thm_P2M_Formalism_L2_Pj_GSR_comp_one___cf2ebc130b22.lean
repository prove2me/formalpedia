-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Pj_GSR_comp_one___cf2ebc130b22
-- name    : P2M_Formalism_L2_Pj_GSR_comp_one___cf2ebc130b22
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:49:03.719544+00:00
-- url     : https://prove2.me/theorems/67147a75-c887-499e-b003-55db2acda54f
-- title:
--   P2 M Formalism L2 Pj GSR comp one   cf2ebc130b22: P2 M Formalism L2 Pj GSR comp one   cf2ebc130b22
-- statement:
--   The P2 M Formalism L2 Pj GSR comp one   cf2ebc130b22 construction uses the P2 M Formalism L2 Pj GSR comp one   cf2ebc130b22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecRel.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecRel.lean#L41-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one___d94ad01bda45

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GSR
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : IsGrpPullback G' G f F) {k : Type} [CommRing k] (tk : Spec (CommRingCat.of k) ⟶ S') (g : Spec (CommRingCat.of k) ⟶ S)
  (hg : tk ≫ f = g)
variable {tk g}

theorem P2M_Formalism_L2_Pj_GSR_comp_one___cf2ebc130b22 {T : Scheme.{0}} {X Y M : Over T} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by sorry

alias «Formalism».«L2».«Pj».«GSR».«comp_one''» := P2M_Formalism_L2_Pj_GSR_comp_one___cf2ebc130b22

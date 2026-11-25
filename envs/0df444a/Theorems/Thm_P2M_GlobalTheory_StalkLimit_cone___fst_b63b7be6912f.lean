-- Prove2me | Theorems.Thm_P2M_GlobalTheory_StalkLimit_cone___fst_b63b7be6912f
-- name    : P2M_GlobalTheory_StalkLimit_cone___fst_b63b7be6912f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:51.995056+00:00
-- url     : https://prove2.me/theorems/6227e19d-ef7b-44de-98e5-00d257b6e09e
-- title:
--   P2 M Global Theory Stalk Limit cone   fst b63b7be6912f: P2 M Global Theory Stalk Limit cone   fst b63b7be6912f
-- statement:
--   The P2 M Global Theory Stalk Limit cone   fst b63b7be6912f construction uses the P2 M Global Theory Stalk Limit cone   fst b63b7be6912f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L107-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.StalkLimit
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
variable {S X : Scheme.{u}} (x : S) (p : X ⟶ S)
variable {x p} {X' : Scheme.{u}} {φ : X' ⟶ X} {p' : X' ⟶ Spec (S.presheaf.stalk x)}

theorem P2M_GlobalTheory_StalkLimit_cone___fst_b63b7be6912f (h : IsPullback φ p' p (S.fromSpecStalk x)) (V : AffNhd x) :
    (cone h).π.app V ≫ pullback.fst p V.1.ι = φ := by sorry

alias «GlobalTheory».«StalkLimit».«cone_π_fst» := P2M_GlobalTheory_StalkLimit_cone___fst_b63b7be6912f

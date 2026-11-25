-- Prove2me | Theorems.Thm_P2M_MainStatements_Hodge_Pf_AXO_isPullO_id__c9a67d2b14ee
-- name    : P2M_MainStatements_Hodge_Pf_AXO_isPullO_id__c9a67d2b14ee
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:56:59.76981+00:00
-- url     : https://prove2.me/theorems/d79b81fc-176c-46a3-b881-ffc4bf282fc0
-- title:
--   P2 M Main Statements Hodge Pf AXO is Pull O id  c9a67d2b14ee: P2 M Main Statements Hodge Pf AXO is Pull O id  c9a67d2b14ee
-- statement:
--   The P2 M Main Statements Hodge Pf AXO is Pull O id  c9a67d2b14ee construction uses the P2 M Main Statements Hodge Pf AXO is Pull O id  c9a67d2b14ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianPullbackLattices/CompositeRestrictionPullInjective.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianPullbackLattices/CompositeRestrictionPullInjective.lean#L92-L94

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_CompositeRestrictionPullInjective
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open MainStatements MainStatements.Hodge MainStatements.Hodge.Pf MainStatements.Hodge.Pf.AXO
variable {R : Type} [CommRing R]

theorem P2M_MainStatements_Hodge_Pf_AXO_isPullO_id__c9a67d2b14ee {X : Scheme.{0}} (s : X ⟶ Sp R) (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R))
    (c : HO1 s) : IsPullO h c c := by sorry

alias «MainStatements».«Hodge».«Pf».«AXO».«isPullO_id'» := P2M_MainStatements_Hodge_Pf_AXO_isPullO_id__c9a67d2b14ee

-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_CechAcyclic_of_shortExact__c77d04db8925
-- name    : P2M_GroundTheory_Arith_SchemeCoh_CechAcyclic_of_shortExact__c77d04db8925
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:24.429826+00:00
-- url     : https://prove2.me/theorems/70952dcd-7eb9-41e9-ae44-7bdb5df4ba50
-- title:
--   P2 M Ground Theory Arith Scheme Coh Cech Acyclic of short Exact  c77d04db8925: P2 M Ground Theory Arith Scheme Coh Cech Acyclic of short Exact  c77d04db8925
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh Cech Acyclic of short Exact  c77d04db8925 construction uses the P2 M Ground Theory Arith Scheme Coh Cech Acyclic of short Exact  c77d04db8925 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L96-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L96-L117

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
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
open CategoryTheory Opposite TopologicalSpace Limits
universe w u
variable {X : TopCat.{u}}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P)
variable {P}

theorem P2M_GroundTheory_Arith_SchemeCoh_CechAcyclic_of_shortExact__c77d04db8925 {ι : Type w} (U : ι → Opens X)
    {F I Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ I) (g : I ⟶ Q) (hfg : f ≫ g = 0)
    (hinj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Injective (f.app (op (inter U i))))
    (hex : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (y : I.obj (op (inter U i))),
      g.app _ y = 0 → ∃ x, f.app _ x = y)
    (hsurj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Surjective (g.app (op (inter U i))))
    (hF : CechAcyclic F U) (hI : CechAcyclic I U) : CechAcyclic Q U := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«CechAcyclic».«of_shortExact'» := P2M_GroundTheory_Arith_SchemeCoh_CechAcyclic_of_shortExact__c77d04db8925

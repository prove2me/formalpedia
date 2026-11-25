-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_homologyFunctorIso__moduleLeftHomologyData_apply_b9da34f1dace
-- name    : P2M_GroundTheory_GroupCoh_homologyFunctorIso__moduleLeftHomologyData_apply_b9da34f1dace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:51.538051+00:00
-- url     : https://prove2.me/theorems/a52abc13-2287-4d7d-8277-f500dbe0caea
-- title:
--   P2 M Ground Theory Group Coh homology Functor Iso  module Left Homology Data apply b9da34f1dace: P2 M Ground Theory Group Coh homology Functor Iso  module Left Homology Data apply b9da34f1dace
-- statement:
--   The P2 M Ground Theory Group Coh homology Functor Iso  module Left Homology Data apply b9da34f1dace construction uses the P2 M Ground Theory Group Coh homology Functor Iso  module Left Homology Data apply b9da34f1dace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ModuleHomologyData.lean#L129-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ModuleHomologyData.lean#L129-L157

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits
universe u
variable {R : Type u} [CommRing R]

theorem P2M_GroundTheory_GroupCoh_homologyFunctorIso__moduleLeftHomologyData_apply_b9da34f1dace {ιc : Type*} {c : ComplexShape ιc}
    (C : HomologicalComplex (ModuleCat.{u} R) c) (i j k : ιc) (hi : c.prev j = i)
    (hk : c.next j = k) (K : Type u) [AddCommGroup K] [Module R K]
    (ι : K →ₗ[R] (C.sc' i j k).X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker (C.sc' i j k).g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range (C.sc' i j k).f.hom)
    (z : C.cycles j) (x : K) (hx : ι x = (C.iCycles j).hom z) :
    (moduleLeftHomologyData _ K ι hι hrange N hN).homologyIso.hom.hom
      (((HomologicalComplex.homologyFunctorIso' _ c i j k hi hk).hom.app C).hom
        ((C.homologyπ j).hom z)) = Submodule.Quotient.mk x := by sorry

alias «GroundTheory».«GroupCoh».«homologyFunctorIso'_moduleLeftHomologyData_apply» := P2M_GroundTheory_GroupCoh_homologyFunctorIso__moduleLeftHomologyData_apply_b9da34f1dace
